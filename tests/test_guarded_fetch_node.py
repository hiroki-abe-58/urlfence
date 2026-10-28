"""`examples/guarded_fetch.mjs`, the Node counterpart of `examples/guarded_fetch.py`, end to end with
the real `urlfence` binary and nothing leaving the machine.

The tests run `tests/guarded_fetch_node.mjs` under node, which calls the example and reports what it
did. There, every `net.Socket` connect call is recorded with the host and port the example gave
it, then sent to an origin fixture on 127.0.0.1 instead (as tests/test_guarded_fetch.py replaces
`open_socket`, one level lower, so the example's own connection code runs); `dns.lookup` and
`dns.promises.lookup` refuse and are recorded, so Node resolves nothing; and the resolver given to
`guardedFetch` answers from a table (one list per lookup, so an answer can change between hops). The
answers are public addresses where a fetch should succeed, so URLFence's address policy needs no
exception for the fixture: only the driver knows that the connection ends on 127.0.0.1. The names
are under `.invalid`, so that none of them could resolve even if something got past the guard.

The origin fixture records what each connection brings first: an HTTP request head, answered from
PAGES by its Host header and path, or a TLS ClientHello, answered with a fatal alert. With openssl,
https fixtures complete the handshake with throwaway self-signed certificates made for the run, to
see which name the certificate is checked against. Unusable answers from the binary come from a
stand-in binary (`URLFENCE_BIN`) that prints what a test asks for.

Skipped if node (or, for the certificate tests, openssl) is not installed, unless URLFENCE_REQUIRE,
a comma-separated list, names it: then a missing tool fails, as in CI."""
import base64
import json
import os
import shutil
import socketserver
import ssl
import subprocess
import sys
import tempfile
import threading
import time
import unittest
import urllib.parse

import compat
from common import BIN, NODE, ROOT, run_check

DRIVER = os.path.join(ROOT, "tests", "guarded_fetch_node.mjs")
OPENSSL = shutil.which("openssl")
REQUIRED = {t for t in os.environ.get("URLFENCE_REQUIRE", "").split(",") if t}
# Variables that change what node or the example does; no run inherits them.
CLEAN = ("http_proxy", "HTTP_PROXY", "https_proxy", "HTTPS_PROXY", "no_proxy", "NO_PROXY", "all_proxy", "ALL_PROXY",
         "NODE_USE_ENV_PROXY", "NODE_OPTIONS", "NODE_TLS_REJECT_UNAUTHORIZED", "NODE_EXTRA_CA_CERTS")

PAGES = {
    ("docs.example.invalid", "/guide"): (200, {}, b"the guide"),
    ("docs.example.invalid", "/moved"): (302, {"Location": "/guide"}, b""),
    ("docs.example.invalid", "/relative"): (302, {"Location": "guide"}, b""),
    ("docs.example.invalid", "/upper"): (302, {"Location": "http://DOCS.example.invalid/guide"}, b""),
    ("docs.example.invalid", "/sneaky"): (302, {"Location": "http://docs.example.invalid@evil.example.invalid/"}, b""),
    ("docs.example.invalid", "/loop"): (302, {"Location": "/loop"}, b""),
    ("docs.example.invalid", "/broken"): (404, {"Transfer-Encoding": "chunked"}, b"zz\r\n"),
    ("docs.example.invalid", "/large"): (200, {}, b"z" * 50_000),
    # Content-Length says 100 bytes; the fixture sends these and closes the connection.
    ("docs.example.invalid", "/short"): (200, {"Content-Length": "100"}, b"0123456789"),
    ("docs.example.invalid", "/short404"): (404, {"Content-Length": "100"}, b"gone"),
    ("docs.example.invalid", "/short302"): (302, {"Location": "/guide", "Content-Length": "100"}, b"ab"),
    # A 304 has no body, whatever Content-Length says.
    ("docs.example.invalid", "/not-modified"): (304, {"Content-Length": "100"}, b""),
    ("docs.example.invalid", "/to-api"): (302, {"Location": "http://api.example.invalid/data"}, b""),
    ("api.example.invalid", "/data"): (200, {}, b"api data"),
    ("8.8.8.8", "/guide"): (200, {}, b"the guide by address"),
}
for code in (301, 302, 303, 307, 308):
    PAGES[("docs.example.invalid", f"/leave{code}")] = (code, {"Location": "http://evil.example.invalid/collect"}, b"")
ALLOW = {"allow": ["docs.example.invalid"], "schemes": ["http"]}
# As in tests/test_guarded_fetch.py: bodies cut short of their Content-Length, which refuse, and
# answers that are not cut short, which do not.
SHORT = ("/short", "/short404", "/short302")
NOT_SHORT = (("/short", {"maxBytes": 5}, (200, b"01234")), ("/short", {"maxBytes": 0}, (200, b"")),
             ("/not-modified", {}, (304, b"")), ("/missing", {}, (404, b"not found")))
# A Location in raw forms (written with | for a backslash and _ for a tab): WHATWG removes the tab,
# reads the backslashes as slashes, decodes and lowercases the host, and drops the default port and
# the dot segments, giving http://docs.example.invalid/guide?q=1.
RAW = "http:||DOCS%2Eexa_mple.invalid:80|a|..|%2e%2e|guide?q=1".replace("|", chr(92)).replace("_", chr(9))
PAGES[("docs.example.invalid", "/raw")] = (302, {"Location": RAW}, b"")
PAGES[("docs.example.invalid", "/numeric")] = (302, {"Location": "http://0x7f.1/guide"}, b"")
REFUSED_EVERYWHERE = [  # (answers, nat64): each has an answer URLFence does not allow
    (["127.0.0.1"], []), (["10.0.0.1"], []), (["169.254.169.254"], []), (["100.100.100.200"], []),
    (["192.0.0.192"], []), (["::1"], []), (["::ffff:127.0.0.1"], []), (["::ffff:a9fe:a9fe"], []),
    (["::127.0.0.1"], []), (["64:ff9b::a9fe:a9fe"], []), (["64:ff9b::a9fe:a9fe"], ["64:ff9b::/96"]),
    (["64:ff9b:1::a00:1"], []), (["2002:7f00:1::1"], []), (["2001:0:4136:e378:8000:63bf:3fff:fdd2"], []),
    (["2606:4700::5efe:a9fe:a9fe"], []), (["fd00:ec2::254"], []), (["fe80::1%2"], []), (["fec0::1"], []),
    (["8.8.8.8", "127.0.0.1"], []), (["127.0.0.1", "8.8.8.8"], []),
    (["2606:4700:4700::1111", "::ffff:169.254.169.254"], []),
]

# A stand-in for the binary: prints what FAKE_URLFENCE asks for its subcommand, else runs the real one.
FAKE = """#!{python}
import base64, json, os, sys, time
want = json.loads(os.environ.get("FAKE_URLFENCE", "{{}}")).get(sys.argv[1])
if want is None:
    os.execv({real!r}, [{real!r}] + sys.argv[1:])
time.sleep(want.get("sleep", 0))
sys.stdout.buffer.write(base64.b64decode(want.get("out", "")))
sys.stderr.buffer.write(base64.b64decode(want.get("err", "")))
sys.exit(want.get("code", 0))
"""


def need(tool, path):
    if path is None:
        if tool in REQUIRED:
            raise AssertionError(f"{tool} is not installed, and URLFENCE_REQUIRE requires it")
        raise unittest.SkipTest(f"{tool} is not installed")


def node(items, env=None, lookups=False, violations=False):
    """Run the driver on these items and return their results. Nothing may connect anywhere but the
    fixtures (unless `violations`: then what the driver refused is for the test to check), and node
    itself may resolve nothing (unless `lookups`)."""
    full = {k: v for k, v in os.environ.items() if k not in CLEAN}
    full.update({"URLFENCE_BIN": BIN, **(env or {})})
    p = subprocess.run([NODE, DRIVER], input=json.dumps({"items": items}).encode(), capture_output=True, env=full,
                       timeout=120, check=False)
    if p.returncode != 0:
        raise AssertionError(f"driver failed (exit {p.returncode}): {p.stderr.decode(errors='replace')}")
    results = json.loads(p.stdout.decode().splitlines()[-1])["results"]
    for r in results:
        if (r["violations"] and not violations) or (r["lookups"] and not lookups):
            raise AssertionError(f"connections {r['violations']}, lookups {r['lookups']}")
    return results


def confined(test):
    """A connect to 0.0.0.0 would reach the driver's listener on 127.0.0.1: the driver must refuse
    it, and nothing arrive, before a test tries 192.0.2.1 (TEST-NET-1)."""
    r = node([{"op": "openSocket", "addr": "0.0.0.0"}], violations=True)[0]
    test.assertEqual((r["accepted"], len(r["violations"])), (0, 1))
    test.assertTrue(r["violations"][0].startswith("connect 0.0.0.0:"))


def ok(r):
    if "ok" not in r:
        raise AssertionError(f"expected an answer, got {r.get('error')}")
    out = dict(r["ok"])
    if "body" in out:
        out["body"] = base64.b64decode(out["body"])
    return out


def refused(r, name="Refused"):
    if r.get("error", {}).get("name") != name:
        raise AssertionError(f"expected {name}, got {r}")
    return r["error"]


def fake(code=0, out=b"", err=b"", sleep=0):
    return {"code": code, "out": base64.b64encode(out).decode(), "err": base64.b64encode(err).decode(), "sleep": sleep}


def respond(data):
    lines = data.split(b"\r\n\r\n", 1)[0].decode("latin-1").split("\r\n")
    path = (lines[0].split(" ") + ["", ""])[1].split("?")[0]
    host = (compat.header(lines, "Host") or "").rsplit(":", 1)[0]
    status, headers, body = PAGES.get((host, path), (404, {}, b"not found"))
    head = f"HTTP/1.1 {status} X\r\nConnection: close\r\n"
    if "Transfer-Encoding" not in headers and "Content-Length" not in headers:
        head += f"Content-Length: {len(body)}\r\n"
    head += "".join(f"{k}: {v}\r\n" for k, v in headers.items())
    return head.encode() + b"\r\n" + body


def heads(records):
    """The request line and Host header of each HTTP request in `records`."""
    out = []
    for data in records:
        lines = data.split(b"\r\n\r\n", 1)[0].decode("latin-1").split("\r\n")
        out.append((lines[0], compat.header(lines, "Host")))
    return out


class Origin:
    """A TCP listener on 127.0.0.1 that records the first bytes of each connection, then answers an
    HTTP request from PAGES, or a TLS ClientHello with a fatal alert. With `cert`, it completes TLS
    handshakes with that certificate instead, records each server name (`names`) and each request
    that arrives over TLS, and answers it from PAGES."""

    def __init__(self, cert=None):
        self.records, self.names = [], []
        origin = self
        context = None
        if cert is not None:
            context = ssl.SSLContext(ssl.PROTOCOL_TLS_SERVER)
            context.load_cert_chain(*cert)
            context.sni_callback = lambda _sock, name, _ctx: self.names.append(name)

        class Handler(socketserver.BaseRequestHandler):
            def handle(self):
                conn = self.request
                conn.settimeout(5)
                data = b""
                try:
                    if context is not None:
                        conn = context.wrap_socket(conn, server_side=True)
                    while len(data) < 65536 and not compat.message_complete(data):
                        chunk = conn.recv(4096)
                        if not chunk:
                            break
                        data += chunk
                except OSError:  # ssl.SSLError included: the client refused the certificate
                    pass
                if data:
                    origin.records.append(data)
                answer = compat.TLS_ALERT if data[:1] == b"\x16" else respond(data)
                try:
                    conn.sendall(answer)
                except OSError:
                    pass
                if conn is not self.request:
                    conn.close()

        self.server = socketserver.ThreadingTCPServer(("127.0.0.1", 0), Handler)
        self.server.daemon_threads = True
        self.port = self.server.server_address[1]
        threading.Thread(target=self.server.serve_forever, args=(0.01,), daemon=True).start()

    def close(self):
        self.server.shutdown()
        self.server.server_close()


class NodeTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        need("node", NODE)

    def setUp(self):
        self.origin = Origin()
        self.addCleanup(self.origin.close)

    def item(self, url, answers, **kw):
        extra = {k: kw.pop(k) for k in ("ca", "agent", "env", "origin") if k in kw}
        return {"op": "fetch", "url": url, "answers": answers, "origin": self.origin.port,
                "options": {**ALLOW, **kw}, **extra}

    def fetch(self, url, answers, env=None, **kw):
        return node([self.item(url, answers, **kw)], env)[0]


class Pinned(NodeTest):
    def test_a_checked_address_is_connected_to_and_the_host_is_kept(self):
        r = self.fetch("http://docs.example.invalid/guide?v=3#top", {"docs.example.invalid": [["8.8.8.8"]]})
        out = ok(r)
        self.assertEqual((out["status"], out["body"]), (200, b"the guide"))
        self.assertEqual(r["connects"], [["8.8.8.8", 80]])
        self.assertEqual(r["resolves"], [["docs.example.invalid", {"all": True}]])
        self.assertEqual(heads(self.origin.records), [("GET /guide?v=3 HTTP/1.1", "docs.example.invalid")])
        self.assertEqual(out["hops"][0]["addrs"], [{"addr": "8.8.8.8", "decision": "allow", "reason": None}])
        self.assertEqual(out["hops"][0]["connected"], "8.8.8.8")

    def test_the_request_is_for_exactly_the_checked_url(self):
        urls = {"http://docs.example.invalid/guide?v=3;a=//b": "GET /guide?v=3;a=//b HTTP/1.1",
                "http://docs.example.invalid/a/../guide": "GET /a/../guide HTTP/1.1",
                "http://docs.example.invalid?x=1#f": "GET /?x=1 HTTP/1.1"}
        rs = node([self.item(u, {"docs.example.invalid": [["8.8.8.8"]]}) for u in urls])
        for r in rs:
            ok(r)
        self.assertEqual(heads(self.origin.records), [(line, "docs.example.invalid") for line in urls.values()])

    def test_port_and_ipv6(self):
        rs = node([self.item("http://docs.example.invalid:8080/guide",
                             {"docs.example.invalid": [["2606:4700:4700::1111"]]}),
                   self.item("http://docs.example.invalid:80/guide", {"docs.example.invalid": [["8.8.8.8"]]})])
        self.assertEqual([ok(r)["status"] for r in rs], [200, 200])
        self.assertEqual([r["connects"] for r in rs], [[["2606:4700:4700::1111", 8080]], [["8.8.8.8", 80]]])
        self.assertEqual(heads(self.origin.records), [("GET /guide HTTP/1.1", "docs.example.invalid:8080"),
                                                      ("GET /guide HTTP/1.1", "docs.example.invalid")])

    def test_every_answer_is_checked_before_any_connection(self):
        rs = node([self.item("http://docs.example.invalid/guide", {"docs.example.invalid": [addrs]}, nat64=nat64)
                   for addrs, nat64 in REFUSED_EVERYWHERE])
        for (addrs, nat64), r in zip(REFUSED_EVERYWHERE, rs):
            with self.subTest(addrs=addrs, nat64=nat64):
                e = refused(r)
                self.assertTrue(any(a["decision"] != "allow" for a in e["hops"][-1]["addrs"]))
                self.assertEqual(r["connects"], [])
        self.assertEqual(self.origin.records, [])

    def test_a_configured_nat64_prefix_decides_on_the_ipv4_address(self):
        good, bad = node([
            self.item("http://docs.example.invalid/guide", {"docs.example.invalid": [["64:ff9b::808:808"]]},
                      nat64=["64:ff9b::/96"]),
            # A prefix nat64Ok would ignore is a usage error, and the fetch refuses.
            self.item("http://docs.example.invalid/guide", {"docs.example.invalid": [["64:ff9b:1::808:808"]]},
                      nat64=["64:ff9b:1::/96"])])
        self.assertEqual(ok(good)["status"], 200)
        self.assertEqual(good["connects"], [["64:ff9b::808:808", 80]])
        self.assertIn("urlfence: ", refused(bad)["message"])
        self.assertEqual(bad["connects"], [])

    def test_deny_addr(self):
        r = self.fetch("http://docs.example.invalid/guide", {"docs.example.invalid": [["8.8.8.8"]]},
                       denyAddr=["8.8.0.0/16"])
        self.assertIn("deny 8.8.0.0/16", refused(r)["message"])
        self.assertEqual(r["connects"], [])

    def test_an_answer_that_changes_between_hops_is_checked_again(self):
        # Public on the first lookup, loopback on the second: the redirect is not followed.
        r = self.fetch("http://docs.example.invalid/moved", {"docs.example.invalid": [["8.8.8.8"], ["127.0.0.1"]]})
        hops = refused(r)["hops"]
        self.assertEqual([h["url"] for h in hops],
                         ["http://docs.example.invalid/moved", "http://docs.example.invalid/guide"])
        self.assertEqual(hops[1]["addrs"][0]["decision"], "deny")
        self.assertEqual(r["connects"], [["8.8.8.8", 80]])
        self.assertEqual([h for h, _ in r["resolves"]], ["docs.example.invalid", "docs.example.invalid"])

    def test_a_redirect_to_an_allowed_host_with_a_denied_address_is_not_followed(self):
        allow = ["docs.example.invalid", "api.example.invalid"]
        denied, fine = node([
            self.item("http://docs.example.invalid/to-api", {"docs.example.invalid": [["8.8.8.8"]],
                                                         "api.example.invalid": [["10.0.0.1"]]}, allow=allow),
            self.item("http://docs.example.invalid/to-api", {"docs.example.invalid": [["8.8.8.8"]],
                                                         "api.example.invalid": [["1.1.1.1"]]}, allow=allow)])
        hops = refused(denied)["hops"]
        self.assertEqual([(h["url"], h["decision"]) for h in hops],
                         [("http://docs.example.invalid/to-api", "allow"),
                          ("http://api.example.invalid/data", "allow")])
        self.assertEqual(hops[1]["addrs"][0]["decision"], "deny")
        self.assertEqual(denied["connects"], [["8.8.8.8", 80]])
        self.assertEqual(ok(fine)["body"], b"api data")
        self.assertEqual(fine["connects"], [["8.8.8.8", 80], ["1.1.1.1", 80]])
        self.assertEqual(heads(self.origin.records), [("GET /to-api HTTP/1.1", "docs.example.invalid")] * 2
                         + [("GET /data HTTP/1.1", "api.example.invalid")])

    def test_https_uses_the_url_host_as_server_name(self):
        # The fixture ends the handshake with an alert, so the fetch fails after the ClientHello.
        r = self.fetch("https://docs.example.invalid/guide", {"docs.example.invalid": [["8.8.8.8"]]}, schemes=["https"])
        refused(r)
        self.assertEqual(r["connects"], [["8.8.8.8", 443]])
        self.assertEqual([compat.client_hello_names(d) for d in self.origin.records], [["docs.example.invalid"]])

    def test_an_ip_host_allowed_by_the_url_check_is_still_checked(self):
        r = self.fetch("http://127.0.0.1/guide", {"127.0.0.1": [["127.0.0.1"]]}, allow=["127.0.0.1"])
        refused(r)
        self.assertEqual(r["connects"], [])

    def test_no_lookup_for_a_refused_url_and_no_connection_without_an_answer(self):
        rs = node([self.item("http://evil.example.invalid/", {"evil.example.invalid": [["8.8.8.8"]]}),
                   self.item("http://docs.example.invalid/guide", {}),
                   self.item("http://docs.example.invalid/guide", {"docs.example.invalid": [[]]})])
        self.assertEqual(rs[0]["resolves"], [])
        self.assertIn("could not resolve", refused(rs[1])["message"])
        self.assertIn("has no address", refused(rs[2])["message"])
        self.assertEqual([r["connects"] for r in rs], [[], [], []])

    def test_one_lookup_per_hop(self):
        # The resolver throws on any lookup beyond the ones each hop needs; node itself resolves
        # nothing (the driver refuses and reports dns.lookup).
        rs = node([self.item("http://docs.example.invalid/guide", {"docs.example.invalid": [["8.8.8.8"], "throw"]}),
                   self.item("http://docs.example.invalid/moved",
                             {"docs.example.invalid": [["8.8.8.8"], ["8.8.8.8"], "throw"]}),
                   self.item("http://docs.example.invalid/guide", {"docs.example.invalid": ["throw"]})])
        self.assertEqual([ok(r)["status"] for r in rs[:2]], [200, 200])
        self.assertEqual([len(r["resolves"]) for r in rs], [1, 2, 1])
        self.assertIn("could not resolve", refused(rs[2])["message"])
        self.assertEqual([r["connects"] for r in rs], [[["8.8.8.8", 80]], [["8.8.8.8", 80]] * 2, []])

    def test_the_default_resolver_is_dns_promises_lookup(self):
        item = self.item("http://docs.example.invalid/guide", None)
        del item["answers"]
        r = node([item], lookups=True)[0]
        self.assertIn("could not resolve", refused(r)["message"])
        self.assertEqual((r["lookups"], r["connects"]), (["docs.example.invalid"], []))

    def test_every_redirect_is_checked(self):
        rs = node([self.item("http://docs.example.invalid" + p, {"docs.example.invalid": [["8.8.8.8"]]})
                   for p in ("/moved", "/relative", "/upper")])
        # Location is resolved as WHATWG does: `http://DOCS.example.invalid/guide` becomes lowercase.
        for r in rs:
            out = ok(r)
            self.assertEqual(out["status"], 200)
            self.assertEqual(out["hops"][1]["url"], "http://docs.example.invalid/guide")

    def test_a_redirect_target_is_normalised_then_checked_and_requested_exactly(self):
        rs = node([self.item("http://docs.example.invalid/raw", {"docs.example.invalid": [["8.8.8.8"]]}),
                   self.item("http://docs.example.invalid/numeric", {"docs.example.invalid": [["8.8.8.8"]],
                                                                     "127.0.0.1": [["127.0.0.1"]]},
                             allow=["docs.example.invalid", "127.0.0.1"])])
        out = ok(rs[0])
        self.assertEqual([h["url"] for h in out["hops"]],
                         ["http://docs.example.invalid/raw", "http://docs.example.invalid/guide?q=1"])
        self.assertEqual(out["body"], b"the guide")
        self.assertEqual(heads(self.origin.records[:2]), [("GET /raw HTTP/1.1", "docs.example.invalid"),
                                                          ("GET /guide?q=1 HTTP/1.1", "docs.example.invalid")])
        # guarded_fetch.py would check urljoin's result, which keeps the raw forms and is refused.
        joined = urllib.parse.urljoin("http://docs.example.invalid/raw", RAW)
        self.assertEqual(run_check([joined], ["docs.example.invalid"], schemes=["http"])[1][0]["decision"], "reject")
        # `0x7f.1` becomes 127.0.0.1: allowed by the URL check here, refused by the address check.
        hops = refused(rs[1])["hops"]
        self.assertEqual([(h["url"], h["decision"]) for h in hops],
                         [("http://docs.example.invalid/numeric", "allow"), ("http://127.0.0.1/guide", "allow")])
        self.assertEqual(hops[1]["addrs"][0]["decision"], "deny")
        self.assertEqual(rs[1]["connects"], [["8.8.8.8", 80]])
        self.assertEqual(len(self.origin.records), 3)

    def test_tls_options_that_could_turn_verification_off_are_refused(self):
        options = ({"rejectUnauthorized": False}, {"checkServerIdentity": None}, {"session": "x"})
        rs = node([self.item("https://docs.example.invalid/guide", {"docs.example.invalid": [["8.8.8.8"]]},
                             schemes=["https"], tls=t, pin=pin) for t in options for pin in (True, False)])
        for r in rs:
            self.assertIn("is not an option", refused(r, "TypeError")["message"])
            self.assertEqual((r["resolves"], r["connects"]), ([], []))

    def test_a_redirect_to_another_host_is_refused_before_it_is_requested(self):
        cases = [(f"/leave{code}", "deny") for code in (301, 302, 303, 307, 308)] + [("/sneaky", "reject")]
        rs = node([self.item("http://docs.example.invalid" + p, {"docs.example.invalid": [["8.8.8.8"]]})
                   for p, _ in cases])
        for (path, decision), r in zip(cases, rs):
            with self.subTest(path=path):
                self.assertEqual(refused(r)["hops"][-1]["decision"], decision)
                self.assertEqual(len(r["resolves"]), 1)
        self.assertEqual(heads(self.origin.records), [(f"GET {p} HTTP/1.1", "docs.example.invalid") for p, _ in cases])

    def test_refused_urls_are_never_requested(self):
        urls = ("http://docs.example.invalid.evil.example.invalid/",
                "http://docs.example.invalid@evil.example.invalid/",
                "http://DOCS.example.invalid/guide", "http://127.1/", "https://docs.example.invalid/guide")
        answers = {"docs.example.invalid": [["8.8.8.8"]], "docs.example.invalid.evil.example.invalid": [["8.8.8.8"]]}
        for r in node([self.item(u, answers) for u in urls]):
            refused(r)
            self.assertEqual((r["resolves"], r["connects"]), ([], []))
        self.assertEqual(self.origin.records, [])

    def test_a_redirect_loop_stops(self):
        r = self.fetch("http://docs.example.invalid/loop", {"docs.example.invalid": [["8.8.8.8"]]}, maxRedirects=3)
        self.assertEqual(refused(r)["message"], "more than 3 redirects")
        self.assertEqual(len(self.origin.records), 4)

    def test_a_broken_answer_refuses(self):
        r = self.fetch("http://docs.example.invalid/broken", {"docs.example.invalid": [["8.8.8.8"]]})
        self.assertIn("request failed", refused(r)["message"])

    def test_the_body_is_cut_at_max_bytes(self):
        rs = node([self.item("http://docs.example.invalid/large", {"docs.example.invalid": [["8.8.8.8"]]}, **kw)
                   for kw in ({"maxBytes": 1000}, {"maxBytes": 0}, {})])
        self.assertEqual([(ok(r)["status"], ok(r)["body"]) for r in rs],
                         [(200, b"z" * 1000), (200, b""), (200, b"z" * 50_000)])

    def test_a_body_shorter_than_its_content_length_refuses(self):
        answers = {"docs.example.invalid": [["8.8.8.8"]]}
        rs = node([self.item("http://docs.example.invalid" + path, answers) for path in SHORT]
                  + [self.item("http://docs.example.invalid" + path, answers, **kw) for path, kw, _ in NOT_SHORT])
        for r in rs[:len(SHORT)]:
            self.assertIn("request failed", refused(r)["message"])
        self.assertEqual([(ok(r)["status"], ok(r)["body"]) for r in rs[len(SHORT):]],
                         [answer for _, _, answer in NOT_SHORT])


class Proxies(NodeTest):
    URL = "http://docs.example.invalid/guide"
    ANSWERS = {"docs.example.invalid": [["8.8.8.8"]]}

    def test_a_proxy_node_would_use_refuses_before_anything_is_resolved(self):
        proxy = "http://127.0.0.1:9"
        envs = [{"NODE_USE_ENV_PROXY": "1", "HTTP_PROXY": proxy}, {"NODE_USE_ENV_PROXY": "1", "http_proxy": proxy},
                {"NODE_USE_ENV_PROXY": "true", "HTTP_PROXY": proxy}]
        rs = node([self.item(self.URL, self.ANSWERS, env=e) for e in envs]
                  + [self.item("https://docs.example.invalid/guide", self.ANSWERS, schemes=["https"],
                               env={"NODE_USE_ENV_PROXY": "1", "HTTPS_PROXY": proxy})])
        for r in rs:
            self.assertIn("proxy", refused(r)["message"])
            self.assertEqual((r["resolves"], r["connects"]), ([], []))

    def test_a_proxy_node_would_not_use_does_not_refuse(self):
        # Node's http module ignores HTTP_PROXY unless its proxy support is on (Node 18 has none),
        # and no proxy is set for http here when only HTTPS_PROXY is.
        proxy = "http://127.0.0.1:9"
        envs = [{"HTTP_PROXY": proxy}, {"NODE_USE_ENV_PROXY": "1", "HTTPS_PROXY": proxy},
                {"NODE_USE_ENV_PROXY": "0", "HTTP_PROXY": proxy}]
        rs = node([self.item(self.URL, self.ANSWERS, env=e) for e in envs])
        for r in rs:
            self.assertEqual(ok(r)["status"], 200)
            self.assertEqual(r["connects"], [["8.8.8.8", 80]])

    def test_an_agent_is_an_error_when_pinned(self):
        r = self.fetch(self.URL, self.ANSWERS, agent=True)
        self.assertIn("pin: false", refused(r, "Error")["message"])
        self.assertEqual((r["resolves"], r["connects"]), ([], []))


class Unpinned(NodeTest):
    def test_node_requests_exactly_the_checked_url_and_redirects_are_still_checked(self):
        rs = node([self.item("http://docs.example.invalid/guide?v=3;a=//b", {}, pin=False),
                   self.item("http://docs.example.invalid/leave302", {}, pin=False),
                   self.item("http://docs.example.invalid/moved", {}, pin=False, agent=True)])
        self.assertEqual(ok(rs[0])["body"], b"the guide")
        self.assertEqual(refused(rs[1])["hops"][-1]["decision"], "deny")
        self.assertEqual(ok(rs[2])["status"], 200)
        # Node connects to the name (resolving it itself, which the driver preempts); no address
        # is checked, and the caller's agent is used.
        self.assertEqual([r["connects"] for r in rs],
                         [[["docs.example.invalid", 80]], [["docs.example.invalid", 80]],
                          [["docs.example.invalid", 80]] * 2])
        self.assertEqual([r["resolves"] for r in rs], [[], [], []])
        self.assertEqual(rs[2].get("agent"), 2)
        self.assertEqual(heads(self.origin.records), [("GET /guide?v=3;a=//b HTTP/1.1", "docs.example.invalid"),
                                                      ("GET /leave302 HTTP/1.1", "docs.example.invalid"),
                                                      ("GET /moved HTTP/1.1", "docs.example.invalid"),
                                                      ("GET /guide HTTP/1.1", "docs.example.invalid")])


class Certificates(NodeTest):
    """https against fixtures that complete the handshake, each with a throwaway self-signed
    certificate for one name: the certificate must match the URL's host, not the address connected
    to, and is verified whatever NODE_TLS_REJECT_UNAUTHORIZED says, pinned or not."""

    @classmethod
    def setUpClass(cls):
        super().setUpClass()
        need("openssl", OPENSSL)
        d = tempfile.mkdtemp()
        cls.addClassCleanup(shutil.rmtree, d)
        cls.certs = {}
        for name, san in (("docs", "DNS:docs.example.invalid"), ("other", "DNS:other.example.invalid"),
                          ("ip", "IP:8.8.8.8")):
            cert, key = os.path.join(d, name + ".pem"), os.path.join(d, name + ".key")
            subprocess.run([OPENSSL, "req", "-x509", "-newkey", "ec", "-pkeyopt", "ec_paramgen_curve:prime256v1",
                            "-nodes", "-days", "1", "-subj", "/CN=urlfence test", "-addext", "subjectAltName=" + san,
                            "-keyout", key, "-out", cert], check=True, capture_output=True)
            with open(cert, encoding="ascii") as f:
                cls.certs[name] = (cert, key, f.read())

    def origin_for(self, name):
        o = Origin(self.certs[name][:2])
        self.addCleanup(o.close)
        return o

    def test_the_certificate_must_match_the_url_host(self):
        origins = {n: self.origin_for(n) for n in self.certs}
        answers = {"docs.example.invalid": [["8.8.8.8"]], "8.8.8.8": [["8.8.8.8"]]}

        def item(url, cert, ca=None, **kw):
            return self.item(url, answers, schemes=["https"], allow=["docs.example.invalid", "8.8.8.8"],
                             ca=self.certs[ca or cert][2], origin=origins[cert].port, **kw)

        rs = node([item("https://docs.example.invalid/guide", "docs"),
                   item("https://docs.example.invalid/guide", "other"),
                   item("https://docs.example.invalid/guide", "ip"),  # a certificate for the address connected to
                   item("https://8.8.8.8/guide", "ip"),
                   item("https://8.8.8.8/guide", "docs")])
        good = ok(rs[0])
        self.assertEqual((good["status"], good["body"], good["hops"][0]["connected"]), (200, b"the guide", "8.8.8.8"))
        self.assertEqual(ok(rs[3])["body"], b"the guide by address")
        for r in (rs[1], rs[2], rs[4]):
            self.assertIn("altnames", refused(r)["message"])
        self.assertEqual([r["connects"] for r in rs], [[["8.8.8.8", 443]]] * 5)
        self.assertEqual(heads(origins["docs"].records), [("GET /guide HTTP/1.1", "docs.example.invalid")])
        self.assertEqual(heads(origins["ip"].records), [("GET /guide HTTP/1.1", "8.8.8.8")])
        self.assertEqual(origins["other"].records, [])
        # The server name is the URL's host, and none for an address (RFC 6066).
        self.assertEqual((origins["docs"].names, origins["other"].names, origins["ip"].names),
                         (["docs.example.invalid", None], ["docs.example.invalid"], ["docs.example.invalid", None]))

    def test_the_certificate_is_verified_by_default(self):
        o = self.origin_for("docs")
        item = self.item("https://docs.example.invalid/guide", {"docs.example.invalid": [["8.8.8.8"]]},
                         schemes=["https"],
                         origin=o.port)
        rs = node([item, {**item, "env": {"NODE_TLS_REJECT_UNAUTHORIZED": "0"}}])
        for r in rs:
            self.assertRegex(refused(r)["message"], "self.signed")  # OpenSSL 1.1 has no hyphen
        self.assertEqual(o.records, [])

    def test_a_body_cut_short_over_https_refuses(self):
        # The origin ends the TLS connection without close_notify, as an injected FIN would.
        o = self.origin_for("docs")
        https = {"schemes": ["https"], "ca": self.certs["docs"][2], "origin": o.port}
        rs = node([self.item("https://docs.example.invalid" + path, {"docs.example.invalid": [["8.8.8.8"]]}, **https)
                   for path in ("/guide", "/short")])
        self.assertEqual(ok(rs[0])["body"], b"the guide")
        self.assertIn("request failed", refused(rs[1])["message"])

    def test_unpinned_requests_verify_the_certificate_too(self):
        docs, other = self.origin_for("docs"), self.origin_for("other")

        def item(origin, **kw):
            return self.item("https://docs.example.invalid/guide", {}, schemes=["https"], pin=False,
                             origin=origin.port, **kw)

        rs = node([item(docs, ca=self.certs["docs"][2]),
                   item(docs, env={"NODE_TLS_REJECT_UNAUTHORIZED": "0"}),
                   item(docs, ca=self.certs["docs"][2], env={"NODE_TLS_REJECT_UNAUTHORIZED": "0"}),
                   item(other, ca=self.certs["other"][2]),
                   item(docs, agent={"rejectUnauthorized": False})])
        self.assertEqual([ok(r)["body"] for r in rs[:1] + rs[2:3]], [b"the guide"] * 2)
        self.assertRegex(refused(rs[1])["message"], "self.signed")
        self.assertIn("altnames", refused(rs[3])["message"])
        # An agent's own options override the example's: this one does not verify.
        self.assertEqual(ok(rs[4])["body"], b"the guide")
        self.assertEqual([r["connects"] for r in rs], [[["docs.example.invalid", 443]]] * 5)
        self.assertEqual([r["resolves"] for r in rs], [[]] * 5)
        self.assertEqual(heads(docs.records), [("GET /guide HTTP/1.1", "docs.example.invalid")] * 3)
        self.assertEqual(other.records, [])


class OpenSocket(NodeTest):
    """The example's own `openSocket`, against the driver's listener on 127.0.0.1, with dns.lookup
    refusing: it connects to a numeric address (also with autoSelectFamily on) and refuses anything
    else with no lookup and no connection."""

    def test_numeric_only(self):
        good = [{"op": "openSocket", "addr": "127.0.0.1", "autoSelectFamily": v} for v in (False, True)]
        bad = [{"op": "openSocket", "addr": a}
               for a in ("localhost", "127.1", "0x7f.0.0.1", "fe80::1%lo", "", "127.0.0.1 ", None)]
        rs = node(good + bad)
        for r in rs[:2]:
            self.assertEqual((r.get("ok"), r["accepted"], len(r["connects"])), (True, 1, 1))
        self.assertEqual([r["autoSelectFamily"] for r in rs[:2]], [False, True])
        for r in rs[2:]:
            self.assertEqual((refused(r, "TypeError")["type"], r["accepted"], r["connects"]), ("TypeError", 0, []))

    def test_the_driver_refuses_other_connections(self):
        # The guard itself: a numeric address that is not the listener's is refused and reported.
        job = {"items": [{"op": "openSocket", "addr": "127.0.0.2"}]}
        p = subprocess.run([NODE, DRIVER], input=json.dumps(job).encode(), capture_output=True,
                           env={k: v for k, v in os.environ.items() if k not in CLEAN}, timeout=60, check=True)
        r = json.loads(p.stdout.decode().splitlines()[-1])["results"][0]
        self.assertEqual((r["accepted"], len(r["violations"])), (0, 1))
        self.assertTrue(r["violations"][0].startswith("connect 127.0.0.2:"))

    def test_nothing_reaches_beyond_loopback(self):
        # The example's openSocket to 192.0.2.1, plain and over TLS: refused before net connects.
        confined(self)
        rs = node([{"op": "openSocket", "addr": "192.0.2.1", "port": 80},
                   {"op": "openSocket", "addr": "192.0.2.1", "port": 443, "tls": "docs.example.invalid"}],
                  violations=True)
        for r, port in zip(rs, (80, 443)):
            with self.subTest(port=port):
                self.assertIn("refusing to connect", refused(r, "Error")["message"])
                self.assertEqual((r["connects"], r["violations"], r["accepted"]),
                                 ([["192.0.2.1", port]], [f"connect 192.0.2.1:{port}"], 0))


class UnusableAnswers(NodeTest):
    URL = "http://docs.example.invalid/guide"

    @classmethod
    def setUpClass(cls):
        super().setUpClass()
        d = tempfile.mkdtemp()
        cls.addClassCleanup(shutil.rmtree, d)
        cls.fake = os.path.join(d, "urlfence")
        with open(cls.fake, "w", encoding="utf-8") as f:
            f.write(FAKE.format(python=sys.executable, real=BIN))
        os.chmod(cls.fake, 0o755)

    def run_fake(self, items):
        return node(items, env={"URLFENCE_BIN": self.fake})

    def check(self, url=URL, options=None, **answer):
        env = {"FAKE_URLFENCE": json.dumps({"check": fake(**answer)} if answer else {})}
        return {"op": "check", "url": url, "options": {**ALLOW, **(options or {})}, "env": env}

    def test_each_refuses(self):
        good = b'{"input":"%s","decision":"allow"}\n' % self.URL.encode()
        cases = ((0, b'{"input":"http://docs.example.invalid/other","decision":"allow"}\n'), (1, good), (3, good),
                 (0, b"not json\n"), (0, b"[]\n"), (0, b""), (0, good + good),
                 (0, b'{"input":"%s"}\n' % self.URL.encode()))
        rs = self.run_fake([self.check(code=c, out=o) for c, o in cases] + [self.check(code=0, out=good)])
        for (code, out), r in zip(cases, rs):
            with self.subTest(code=code, out=out):
                self.assertEqual(ok(r)["decision"], "reject")
        self.assertEqual(ok(rs[-1])["decision"], "allow")  # the stand-in itself works

    def test_a_usage_error_refuses_and_says_why(self):
        r = self.run_fake([self.check(code=2, err=b"urlfence: invalid pattern\n")])[0]
        self.assertEqual((ok(r)["decision"], ok(r)["reason"]), ("reject", "urlfence: urlfence: invalid pattern"))

    def test_a_timeout_is_set_and_refuses(self):
        start = time.monotonic()
        r = self.run_fake([self.check(options={"timeout": 300}, sleep=5, out=b"")])[0]
        self.assertEqual(ok(r), {"decision": "reject", "reason": "urlfence did not run: no answer within 300 ms"})
        self.assertLess(time.monotonic() - start, 4)
        # Node takes 0 as no timeout at all, so it is refused.
        zero = self.run_fake([self.check(options={"timeout": 0}),
                              {"op": "checkAddrs", "addrs": ["8.8.8.8"], "options": {"timeout": 0}},
                              self.item(self.URL, {"docs.example.invalid": [["8.8.8.8"]]}, timeout=0)])
        for r in zero:
            self.assertIn("at least 1 ms", refused(r, "TypeError")["message"])
            self.assertEqual((r["resolves"], r["connects"]), ([], []))

    def test_a_missing_binary_refuses(self):
        r = node([self.check()], env={"URLFENCE_BIN": os.path.join(ROOT, "no-such-urlfence")})[0]
        self.assertEqual(ok(r)["decision"], "reject")
        self.assertTrue(ok(r)["reason"].startswith("urlfence did not run"))

    def test_input_the_binary_cannot_take_refuses(self):
        bad = ("http://docs.example.invalid/a\x00b", "http://docs.example.invalid/\ud800", None)
        for u, r in zip(bad, self.run_fake([self.check(u) for u in bad])):
            with self.subTest(url=repr(u)):
                self.assertEqual(ok(r)["decision"], "reject")

    def test_a_single_string_policy_is_an_error(self):
        rs = self.run_fake([self.check(options={"allow": "docs.example.invalid"}),
                            {"op": "checkAddrs", "addrs": ["8.8.8.8"], "options": {"deny": "10.0.0.0/8"}}])
        for r in rs:
            refused(r, "TypeError")

    def test_unusable_address_answers_refuse(self):
        good = b'{"input":"8.8.8.8","decision":"allow"}\n'
        cases = ((1, good), (0, b'{"input":"8.8.4.4","decision":"allow"}\n'), (0, b""), (0, good + good),
                 (0, b"[]\n"), (2, b""))
        def item(answer):
            return {"op": "checkAddrs", "addrs": ["8.8.8.8"], "options": {},
                    "env": {"FAKE_URLFENCE": json.dumps(answer)}}

        rs = self.run_fake([item({"addr": fake(code=c, out=o)}) for c, o in cases] + [item({})])
        for (code, out), r in zip(cases, rs):
            with self.subTest(code=code, out=out):
                self.assertIsNone(ok(r)["answers"])
        self.assertEqual(ok(rs[-1])["answers"][0]["decision"], "allow")

    def test_a_connection_to_no_fixture_is_refused(self):
        # A fetch with no origin fixture: the driver redirects nothing, so the example's connection
        # to the address the stand-in allows, 192.0.2.1, is refused before net connects.
        confined(self)
        answer = {"input": "192.0.2.1", "decision": "allow", "family": "ipv4", "addr": "192.0.2.1"}
        item = self.item(self.URL, {"docs.example.invalid": [["192.0.2.1"]]},
                         env={"FAKE_URLFENCE": json.dumps({"addr": fake(out=json.dumps(answer).encode() + b"\n")})})
        del item["origin"]
        r = node([item], env={"URLFENCE_BIN": self.fake}, violations=True)[0]
        self.assertIn("refusing to connect", refused(r)["message"])
        self.assertEqual((r["connects"], r["violations"]), ([["192.0.2.1", 80]], ["connect 192.0.2.1:80"]))

    def test_only_the_checked_address_is_connected_to(self):
        # An answer whose printed address is not the checked one refuses, before connecting; one
        # that is the same address in another form is used.
        def answer(inp, addr):
            a = {"input": inp, "decision": "allow", "family": "ipv6" if ":" in inp else "ipv4"}
            if addr is not None:
                a["addr"] = addr
            return {"FAKE_URLFENCE": json.dumps({"addr": fake(out=json.dumps(a).encode() + b"\n")})}

        cases = [("8.8.8.8", a) for a in ("127.0.0.1", "8.8.4.4", "localhost", None, 134744072, "::ffff:8.8.8.8",
                                          "::ffff:808:808", "8.8.8.8 ")]
        rs = self.run_fake([self.item(self.URL, {"docs.example.invalid": [[i]]}, env=answer(i, a)) for i, a in cases]
                           + [self.item(self.URL, {"docs.example.invalid": [["2606:4700:4700::1111"]]},
                                        env=answer("2606:4700:4700::1111", "2606:4700:4700:0:0:0:0:1111"))])
        for (_, a), r in zip(cases, rs):
            with self.subTest(addr=a):
                self.assertIn("urlfence printed", refused(r)["message"])
                self.assertEqual(r["connects"], [])
        self.assertEqual(ok(rs[-1])["status"], 200)
        self.assertEqual(rs[-1]["connects"], [["2606:4700:4700:0:0:0:0:1111", 80]])


if __name__ == "__main__":
    unittest.main()
