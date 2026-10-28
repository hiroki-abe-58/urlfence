"""`examples/guarded_fetch.mjs`, the Node counterpart of `examples/guarded_fetch.py`, end to end with
the real `urlfence` binary and nothing leaving the machine.

The tests run `tests/guarded_fetch_node.mjs` under node, which calls the example and reports what it
did (the last one runs the example's command line). There, every `net.Socket` connect call is
recorded with the host and port the example gave it, then sent to an origin fixture on 127.0.0.1
instead (as tests/test_guarded_fetch.py replaces `open_socket`, one level lower, so the example's
own connection code runs); `dns.lookup` and
`dns.promises.lookup` refuse and are recorded, so Node resolves nothing; and the resolver given to
`guardedFetch` answers from a table (one list per lookup, so an answer can change between hops). The
answers are public addresses where a fetch should succeed, so URLFence's address policy needs no
exception for the fixture: only the driver knows that the connection ends on 127.0.0.1.

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

import compat
from common import BIN, NODE, ROOT

DRIVER = os.path.join(ROOT, "tests", "guarded_fetch_node.mjs")
EXAMPLE = os.path.join(ROOT, "examples", "guarded_fetch.mjs")
OPENSSL = shutil.which("openssl")
REQUIRED = {t for t in os.environ.get("URLFENCE_REQUIRE", "").split(",") if t}
# Variables that change what node or the example does; no run inherits them.
CLEAN = ("http_proxy", "HTTP_PROXY", "https_proxy", "HTTPS_PROXY", "no_proxy", "NO_PROXY", "all_proxy", "ALL_PROXY",
         "NODE_USE_ENV_PROXY", "NODE_OPTIONS", "NODE_TLS_REJECT_UNAUTHORIZED", "NODE_EXTRA_CA_CERTS")

PAGES = {
    ("docs.example.com", "/guide"): (200, {}, b"the guide"),
    ("docs.example.com", "/moved"): (302, {"Location": "/guide"}, b""),
    ("docs.example.com", "/relative"): (302, {"Location": "guide"}, b""),
    ("docs.example.com", "/upper"): (302, {"Location": "http://DOCS.example.com/guide"}, b""),
    ("docs.example.com", "/sneaky"): (302, {"Location": "http://docs.example.com@evil.example.net/"}, b""),
    ("docs.example.com", "/loop"): (302, {"Location": "/loop"}, b""),
    ("docs.example.com", "/broken"): (404, {"Transfer-Encoding": "chunked"}, b"zz\r\n"),
    ("docs.example.com", "/large"): (200, {}, b"z" * 50_000),
    ("docs.example.com", "/to-api"): (302, {"Location": "http://api.example.com/data"}, b""),
    ("api.example.com", "/data"): (200, {}, b"api data"),
    ("8.8.8.8", "/guide"): (200, {}, b"the guide by address"),
}
for code in (301, 302, 303, 307, 308):
    PAGES[("docs.example.com", f"/leave{code}")] = (code, {"Location": "http://evil.example.net/collect"}, b"")
ALLOW = {"allow": ["docs.example.com"], "schemes": ["http"]}
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


def node(items, env=None, lookups=False):
    """Run the driver on these items and return their results. Nothing may connect anywhere but the
    fixtures, and node itself may resolve nothing (unless `lookups`)."""
    full = {k: v for k, v in os.environ.items() if k not in CLEAN}
    full.update({"URLFENCE_BIN": BIN, **(env or {})})
    p = subprocess.run([NODE, DRIVER], input=json.dumps({"items": items}).encode(), capture_output=True, env=full,
                       timeout=120, check=False)
    if p.returncode != 0:
        raise AssertionError(f"driver failed (exit {p.returncode}): {p.stderr.decode(errors='replace')}")
    results = json.loads(p.stdout.decode().splitlines()[-1])["results"]
    for r in results:
        if r["violations"] or (r["lookups"] and not lookups):
            raise AssertionError(f"connections {r['violations']}, lookups {r['lookups']}")
    return results


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
    if "Transfer-Encoding" not in headers:
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
        r = self.fetch("http://docs.example.com/guide?v=3#top", {"docs.example.com": [["8.8.8.8"]]})
        out = ok(r)
        self.assertEqual((out["status"], out["body"]), (200, b"the guide"))
        self.assertEqual(r["connects"], [["8.8.8.8", 80]])
        self.assertEqual(r["resolves"], [["docs.example.com", {"all": True}]])
        self.assertEqual(heads(self.origin.records), [("GET /guide?v=3 HTTP/1.1", "docs.example.com")])
        self.assertEqual(out["hops"][0]["addrs"], [{"addr": "8.8.8.8", "decision": "allow", "reason": None}])
        self.assertEqual(out["hops"][0]["connected"], "8.8.8.8")

    def test_the_request_is_for_exactly_the_checked_url(self):
        urls = {"http://docs.example.com/guide?v=3;a=//b": "GET /guide?v=3;a=//b HTTP/1.1",
                "http://docs.example.com/a/../guide": "GET /a/../guide HTTP/1.1",
                "http://docs.example.com?x=1#f": "GET /?x=1 HTTP/1.1"}
        rs = node([self.item(u, {"docs.example.com": [["8.8.8.8"]]}) for u in urls])
        for r in rs:
            ok(r)
        self.assertEqual(heads(self.origin.records), [(line, "docs.example.com") for line in urls.values()])

    def test_port_and_ipv6(self):
        rs = node([self.item("http://docs.example.com:8080/guide", {"docs.example.com": [["2606:4700:4700::1111"]]}),
                   self.item("http://docs.example.com:80/guide", {"docs.example.com": [["8.8.8.8"]]})])
        self.assertEqual([ok(r)["status"] for r in rs], [200, 200])
        self.assertEqual([r["connects"] for r in rs], [[["2606:4700:4700::1111", 8080]], [["8.8.8.8", 80]]])
        self.assertEqual(heads(self.origin.records), [("GET /guide HTTP/1.1", "docs.example.com:8080"),
                                                      ("GET /guide HTTP/1.1", "docs.example.com")])

    def test_every_answer_is_checked_before_any_connection(self):
        rs = node([self.item("http://docs.example.com/guide", {"docs.example.com": [addrs]}, nat64=nat64)
                   for addrs, nat64 in REFUSED_EVERYWHERE])
        for (addrs, nat64), r in zip(REFUSED_EVERYWHERE, rs):
            with self.subTest(addrs=addrs, nat64=nat64):
                e = refused(r)
                self.assertTrue(any(a["decision"] != "allow" for a in e["hops"][-1]["addrs"]))
                self.assertEqual(r["connects"], [])
        self.assertEqual(self.origin.records, [])

    def test_a_configured_nat64_prefix_decides_on_the_ipv4_address(self):
        good, bad = node([
            self.item("http://docs.example.com/guide", {"docs.example.com": [["64:ff9b::808:808"]]},
                      nat64=["64:ff9b::/96"]),
            # A prefix nat64Ok would ignore is a usage error, and the fetch refuses.
            self.item("http://docs.example.com/guide", {"docs.example.com": [["64:ff9b:1::808:808"]]},
                      nat64=["64:ff9b:1::/96"])])
        self.assertEqual(ok(good)["status"], 200)
        self.assertEqual(good["connects"], [["64:ff9b::808:808", 80]])
        self.assertIn("urlfence: ", refused(bad)["message"])
        self.assertEqual(bad["connects"], [])

    def test_deny_addr(self):
        r = self.fetch("http://docs.example.com/guide", {"docs.example.com": [["8.8.8.8"]]}, denyAddr=["8.8.0.0/16"])
        self.assertIn("deny 8.8.0.0/16", refused(r)["message"])
        self.assertEqual(r["connects"], [])

    def test_an_answer_that_changes_between_hops_is_checked_again(self):
        # Public on the first lookup, loopback on the second: the redirect is not followed.
        r = self.fetch("http://docs.example.com/moved", {"docs.example.com": [["8.8.8.8"], ["127.0.0.1"]]})
        hops = refused(r)["hops"]
        self.assertEqual([h["url"] for h in hops], ["http://docs.example.com/moved", "http://docs.example.com/guide"])
        self.assertEqual(hops[1]["addrs"][0]["decision"], "deny")
        self.assertEqual(r["connects"], [["8.8.8.8", 80]])
        self.assertEqual([h for h, _ in r["resolves"]], ["docs.example.com", "docs.example.com"])

    def test_a_redirect_to_an_allowed_host_with_a_denied_address_is_not_followed(self):
        allow = ["docs.example.com", "api.example.com"]
        denied, fine = node([
            self.item("http://docs.example.com/to-api", {"docs.example.com": [["8.8.8.8"]],
                                                         "api.example.com": [["10.0.0.1"]]}, allow=allow),
            self.item("http://docs.example.com/to-api", {"docs.example.com": [["8.8.8.8"]],
                                                         "api.example.com": [["1.1.1.1"]]}, allow=allow)])
        hops = refused(denied)["hops"]
        self.assertEqual([(h["url"], h["decision"]) for h in hops],
                         [("http://docs.example.com/to-api", "allow"), ("http://api.example.com/data", "allow")])
        self.assertEqual(hops[1]["addrs"][0]["decision"], "deny")
        self.assertEqual(denied["connects"], [["8.8.8.8", 80]])
        self.assertEqual(ok(fine)["body"], b"api data")
        self.assertEqual(fine["connects"], [["8.8.8.8", 80], ["1.1.1.1", 80]])
        self.assertEqual(heads(self.origin.records), [("GET /to-api HTTP/1.1", "docs.example.com")] * 2
                         + [("GET /data HTTP/1.1", "api.example.com")])

    def test_https_uses_the_url_host_as_server_name(self):
        # The fixture ends the handshake with an alert, so the fetch fails after the ClientHello.
        r = self.fetch("https://docs.example.com/guide", {"docs.example.com": [["8.8.8.8"]]}, schemes=["https"])
        refused(r)
        self.assertEqual(r["connects"], [["8.8.8.8", 443]])
        self.assertEqual([compat.client_hello_names(d) for d in self.origin.records], [["docs.example.com"]])

    def test_an_ip_host_allowed_by_the_url_check_is_still_checked(self):
        r = self.fetch("http://127.0.0.1/guide", {"127.0.0.1": [["127.0.0.1"]]}, allow=["127.0.0.1"])
        refused(r)
        self.assertEqual(r["connects"], [])

    def test_no_lookup_for_a_refused_url_and_no_connection_without_an_answer(self):
        rs = node([self.item("http://evil.example.net/", {"evil.example.net": [["8.8.8.8"]]}),
                   self.item("http://docs.example.com/guide", {}),
                   self.item("http://docs.example.com/guide", {"docs.example.com": [[]]})])
        self.assertEqual(rs[0]["resolves"], [])
        self.assertIn("could not resolve", refused(rs[1])["message"])
        self.assertIn("has no address", refused(rs[2])["message"])
        self.assertEqual([r["connects"] for r in rs], [[], [], []])

    def test_one_lookup_per_hop(self):
        # The resolver throws on any lookup beyond the ones each hop needs; node itself resolves
        # nothing (the driver refuses and reports dns.lookup).
        rs = node([self.item("http://docs.example.com/guide", {"docs.example.com": [["8.8.8.8"], "throw"]}),
                   self.item("http://docs.example.com/moved",
                             {"docs.example.com": [["8.8.8.8"], ["8.8.8.8"], "throw"]}),
                   self.item("http://docs.example.com/guide", {"docs.example.com": ["throw"]})])
        self.assertEqual([ok(r)["status"] for r in rs[:2]], [200, 200])
        self.assertEqual([len(r["resolves"]) for r in rs], [1, 2, 1])
        self.assertIn("could not resolve", refused(rs[2])["message"])
        self.assertEqual([r["connects"] for r in rs], [[["8.8.8.8", 80]], [["8.8.8.8", 80]] * 2, []])

    def test_the_default_resolver_is_dns_promises_lookup(self):
        item = self.item("http://docs.example.com/guide", None)
        del item["answers"]
        r = node([item], lookups=True)[0]
        self.assertIn("could not resolve", refused(r)["message"])
        self.assertEqual((r["lookups"], r["connects"]), (["docs.example.com"], []))

    def test_every_redirect_is_checked(self):
        rs = node([self.item("http://docs.example.com" + p, {"docs.example.com": [["8.8.8.8"]]})
                   for p in ("/moved", "/relative", "/upper")])
        # Location is resolved as WHATWG does: `http://DOCS.example.com/guide` becomes lowercase.
        for r in rs:
            out = ok(r)
            self.assertEqual(out["status"], 200)
            self.assertEqual(out["hops"][1]["url"], "http://docs.example.com/guide")

    def test_a_redirect_to_another_host_is_refused_before_it_is_requested(self):
        cases = [(f"/leave{code}", "deny") for code in (301, 302, 303, 307, 308)] + [("/sneaky", "reject")]
        rs = node([self.item("http://docs.example.com" + p, {"docs.example.com": [["8.8.8.8"]]}) for p, _ in cases])
        for (path, decision), r in zip(cases, rs):
            with self.subTest(path=path):
                self.assertEqual(refused(r)["hops"][-1]["decision"], decision)
                self.assertEqual(len(r["resolves"]), 1)
        self.assertEqual(heads(self.origin.records), [(f"GET {p} HTTP/1.1", "docs.example.com") for p, _ in cases])

    def test_refused_urls_are_never_requested(self):
        urls = ("http://docs.example.com.evil.example.net/", "http://docs.example.com@evil.example.net/",
                "http://DOCS.example.com/guide", "http://127.1/", "https://docs.example.com/guide")
        answers = {"docs.example.com": [["8.8.8.8"]], "docs.example.com.evil.example.net": [["8.8.8.8"]]}
        for r in node([self.item(u, answers) for u in urls]):
            refused(r)
            self.assertEqual((r["resolves"], r["connects"]), ([], []))
        self.assertEqual(self.origin.records, [])

    def test_a_redirect_loop_stops(self):
        r = self.fetch("http://docs.example.com/loop", {"docs.example.com": [["8.8.8.8"]]}, maxRedirects=3)
        self.assertEqual(refused(r)["message"], "more than 3 redirects")
        self.assertEqual(len(self.origin.records), 4)

    def test_a_broken_answer_refuses(self):
        r = self.fetch("http://docs.example.com/broken", {"docs.example.com": [["8.8.8.8"]]})
        self.assertIn("request failed", refused(r)["message"])

    def test_the_body_is_cut_at_max_bytes(self):
        rs = node([self.item("http://docs.example.com/large", {"docs.example.com": [["8.8.8.8"]]}, **kw)
                   for kw in ({"maxBytes": 1000}, {"maxBytes": 0}, {})])
        self.assertEqual([(ok(r)["status"], ok(r)["body"]) for r in rs],
                         [(200, b"z" * 1000), (200, b""), (200, b"z" * 50_000)])


class Proxies(NodeTest):
    URL = "http://docs.example.com/guide"
    ANSWERS = {"docs.example.com": [["8.8.8.8"]]}

    def test_a_proxy_node_would_use_refuses_before_anything_is_resolved(self):
        proxy = "http://127.0.0.1:9"
        envs = [{"NODE_USE_ENV_PROXY": "1", "HTTP_PROXY": proxy}, {"NODE_USE_ENV_PROXY": "1", "http_proxy": proxy},
                {"NODE_USE_ENV_PROXY": "true", "HTTP_PROXY": proxy}]
        rs = node([self.item(self.URL, self.ANSWERS, env=e) for e in envs]
                  + [self.item("https://docs.example.com/guide", self.ANSWERS, schemes=["https"],
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
        rs = node([self.item("http://docs.example.com/guide?v=3;a=//b", {}, pin=False),
                   self.item("http://docs.example.com/leave302", {}, pin=False),
                   self.item("http://docs.example.com/moved", {}, pin=False, agent=True)])
        self.assertEqual(ok(rs[0])["body"], b"the guide")
        self.assertEqual(refused(rs[1])["hops"][-1]["decision"], "deny")
        self.assertEqual(ok(rs[2])["status"], 200)
        # Node connects to the name (resolving it itself, which the driver preempts); no address
        # is checked, and the caller's agent is used.
        self.assertEqual([r["connects"] for r in rs],
                         [[["docs.example.com", 80]], [["docs.example.com", 80]], [["docs.example.com", 80]] * 2])
        self.assertEqual([r["resolves"] for r in rs], [[], [], []])
        self.assertEqual(rs[2].get("agent"), 2)
        self.assertEqual(heads(self.origin.records), [("GET /guide?v=3;a=//b HTTP/1.1", "docs.example.com"),
                                                      ("GET /leave302 HTTP/1.1", "docs.example.com"),
                                                      ("GET /moved HTTP/1.1", "docs.example.com"),
                                                      ("GET /guide HTTP/1.1", "docs.example.com")])


class Certificates(NodeTest):
    """Pinned https against fixtures that complete the handshake, each with a throwaway self-signed
    certificate for one name: the certificate must match the URL's host, not the address connected to."""

    @classmethod
    def setUpClass(cls):
        super().setUpClass()
        need("openssl", OPENSSL)
        d = tempfile.mkdtemp()
        cls.addClassCleanup(shutil.rmtree, d)
        cls.certs = {}
        for name, san in (("docs", "DNS:docs.example.com"), ("other", "DNS:other.example.com"), ("ip", "IP:8.8.8.8")):
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
        answers = {"docs.example.com": [["8.8.8.8"]], "8.8.8.8": [["8.8.8.8"]]}

        def item(url, cert, ca=None, **kw):
            return self.item(url, answers, schemes=["https"], allow=["docs.example.com", "8.8.8.8"],
                             ca=self.certs[ca or cert][2], origin=origins[cert].port, **kw)

        rs = node([item("https://docs.example.com/guide", "docs"),
                   item("https://docs.example.com/guide", "other"),
                   item("https://docs.example.com/guide", "ip"),  # a certificate for the address connected to
                   item("https://8.8.8.8/guide", "ip"),
                   item("https://8.8.8.8/guide", "docs")])
        good = ok(rs[0])
        self.assertEqual((good["status"], good["body"], good["hops"][0]["connected"]), (200, b"the guide", "8.8.8.8"))
        self.assertEqual(ok(rs[3])["body"], b"the guide by address")
        for r in (rs[1], rs[2], rs[4]):
            self.assertIn("altnames", refused(r)["message"])
        self.assertEqual([r["connects"] for r in rs], [[["8.8.8.8", 443]]] * 5)
        self.assertEqual(heads(origins["docs"].records), [("GET /guide HTTP/1.1", "docs.example.com")])
        self.assertEqual(heads(origins["ip"].records), [("GET /guide HTTP/1.1", "8.8.8.8")])
        self.assertEqual(origins["other"].records, [])
        # The server name is the URL's host, and none for an address (RFC 6066).
        self.assertEqual((origins["docs"].names, origins["other"].names, origins["ip"].names),
                         (["docs.example.com", None], ["docs.example.com"], ["docs.example.com", None]))

    def test_the_certificate_is_verified_by_default(self):
        o = self.origin_for("docs")
        item = self.item("https://docs.example.com/guide", {"docs.example.com": [["8.8.8.8"]]}, schemes=["https"],
                         origin=o.port)
        rs = node([item, {**item, "env": {"NODE_TLS_REJECT_UNAUTHORIZED": "0"}}])
        for r in rs:
            self.assertRegex(refused(r)["message"], "self.signed")  # OpenSSL 1.1 has no hyphen
        self.assertEqual(o.records, [])


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


class UnusableAnswers(NodeTest):
    URL = "http://docs.example.com/guide"

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
        cases = ((0, b'{"input":"http://docs.example.com/other","decision":"allow"}\n'), (1, good), (3, good),
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

    def test_a_missing_binary_refuses(self):
        r = node([self.check()], env={"URLFENCE_BIN": os.path.join(ROOT, "no-such-urlfence")})[0]
        self.assertEqual(ok(r)["decision"], "reject")
        self.assertTrue(ok(r)["reason"].startswith("urlfence did not run"))

    def test_input_the_binary_cannot_take_refuses(self):
        bad = ("http://docs.example.com/a\x00b", "http://docs.example.com/\ud800", None)
        for u, r in zip(bad, self.run_fake([self.check(u) for u in bad])):
            with self.subTest(url=repr(u)):
                self.assertEqual(ok(r)["decision"], "reject")

    def test_a_single_string_policy_is_an_error(self):
        rs = self.run_fake([self.check(options={"allow": "docs.example.com"}),
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
        rs = self.run_fake([self.item(self.URL, {"docs.example.com": [[i]]}, env=answer(i, a)) for i, a in cases]
                           + [self.item(self.URL, {"docs.example.com": [["2606:4700:4700::1111"]]},
                                        env=answer("2606:4700:4700::1111", "2606:4700:4700:0:0:0:0:1111"))])
        for (_, a), r in zip(cases, rs):
            with self.subTest(addr=a):
                self.assertIn("urlfence printed", refused(r)["message"])
                self.assertEqual(r["connects"], [])
        self.assertEqual(ok(rs[-1])["status"], 200)
        self.assertEqual(rs[-1]["connects"], [["2606:4700:4700:0:0:0:0:1111", 80]])


class Cli(NodeTest):
    def run_cli(self, *args):
        env = {k: v for k, v in os.environ.items() if k not in CLEAN}
        env["URLFENCE_BIN"] = BIN
        return subprocess.run([NODE, EXAMPLE, *args], capture_output=True, env=env, timeout=60, check=False)

    def test_usage_and_a_refusal(self):
        p = self.run_cli("--allow", "docs.example.com")
        self.assertEqual((p.returncode, p.stdout), (2, b""))
        self.assertIn(b"usage:", p.stderr)
        # Refused before anything is resolved: http is not an allowed scheme here.
        p = self.run_cli("--allow", "docs.example.com", "--", "http://docs.example.com/")
        self.assertEqual((p.returncode, p.stdout), (1, b""))
        out = json.loads(p.stderr)
        self.assertEqual([(h["url"], h["decision"]) for h in out["hops"]], [("http://docs.example.com/", "deny")])


if __name__ == "__main__":
    unittest.main()
