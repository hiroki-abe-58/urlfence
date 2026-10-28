"""`examples/guarded_fetch.py` end to end, with the real `urlfence` binary and nothing leaving the
machine.

* Unpinned (`pin=False`): an HTTP proxy on 127.0.0.1 stands in for the web (it serves a few pages
  and records every request). While a test runs, any `getaddrinfo` lookup other than the proxy's
  is refused.
* Pinned (the default): `getaddrinfo` is replaced by a table of answers for each name (one list per
  lookup, so an answer can change between hops), and `gf.open_socket` by a function that records
  the address and port the fetch connects to and connects to an origin fixture on 127.0.0.1
  instead. The answers are public addresses where a fetch should succeed, so URLFence's address
  policy needs no exception for the fixture: only this test function knows that the connection
  ends on 127.0.0.1. The fixture records what each connection brings first (an HTTP request head,
  or a TLS ClientHello, answered with a fatal alert). For one https test, an origin with a
  throwaway self-signed certificate (made with openssl for the run) completes the handshake.

Unusable answers from the binary are simulated by replacing `subprocess.run`. Whatever a test
replaces, tests/common.py refuses any connection beyond loopback and any lookup of a name
(`Confinement` checks it)."""
import http.client
import os
import shutil
import socket
import socketserver
import ssl
import subprocess
import sys
import tempfile
import threading
import unittest
import urllib.request
from unittest import mock

import common
import compat
from common import BIN, ROOT

sys.path.insert(0, os.path.join(ROOT, "examples"))
import guarded_fetch as gf  # noqa: E402

gf.URLFENCE = BIN

PAGES = {
    ("docs.example.com", "/guide"): (200, {}, b"the guide"),
    ("docs.example.com", "/moved"): (302, {"Location": "/guide"}, b""),
    ("docs.example.com", "/sneaky"): (302, {"Location": "http://docs.example.com@evil.example.net/"}, b""),
    ("docs.example.com", "/loop"): (302, {"Location": "/loop"}, b""),
    ("docs.example.com", "/broken"): (404, {"Transfer-Encoding": "chunked"}, b"zz\r\n"),
    ("docs.example.com", "/large"): (200, {}, b"z" * 50_000),
    # Content-Length says 100 bytes; the fixtures send these and close the connection.
    ("docs.example.com", "/short"): (200, {"Content-Length": "100"}, b"0123456789"),
    ("docs.example.com", "/short404"): (404, {"Content-Length": "100"}, b"gone"),
    ("docs.example.com", "/short302"): (302, {"Location": "/guide", "Content-Length": "100"}, b"ab"),
    # A 304 has no body, whatever Content-Length says.
    ("docs.example.com", "/not-modified"): (304, {"Content-Length": "100"}, b""),
}
for code in (301, 302, 303, 307, 308):
    PAGES[("docs.example.com", f"/leave{code}")] = (code, {"Location": "http://evil.example.net/collect"}, b"")
ALLOW = dict(allow=["docs.example.com"], schemes=("http",))
# Bodies cut short of their Content-Length, which refuse, and answers that are not cut short, which
# do not: a body cut at max_bytes (also at 0), a 304 and a complete 404.
SHORT = ("/short", "/short404", "/short302")
# max_bytes values that read the whole body; a short one still refuses.
READ_ALL = ({"max_bytes": None}, {"max_bytes": -1})
NOT_SHORT = (("/short", {"max_bytes": 5}, (200, b"01234")), ("/short", {"max_bytes": 0}, (200, b"")),
             ("/not-modified", {}, (304, b"")), ("/missing", {}, (404, b"not found")))
OPENSSL = shutil.which("openssl")


def throwaway_cert(test, san):
    """(certificate, key) files of a self-signed certificate for `san`, made with openssl for `test`
    and removed after it. Without openssl the test is skipped, unless URLFENCE_REQUIRE (a
    comma-separated list) names it, as in CI: then it fails."""
    if OPENSSL is None:
        if "openssl" in os.environ.get("URLFENCE_REQUIRE", "").split(","):
            raise AssertionError("openssl is not installed, and URLFENCE_REQUIRE requires it")
        raise unittest.SkipTest("openssl is not installed")
    d = tempfile.mkdtemp()
    test.addCleanup(shutil.rmtree, d)
    cert, key = os.path.join(d, "cert.pem"), os.path.join(d, "key.pem")
    subprocess.run([OPENSSL, "req", "-x509", "-newkey", "ec", "-pkeyopt", "ec_paramgen_curve:prime256v1", "-nodes",
                    "-days", "1", "-subj", "/CN=urlfence test", "-addext", "subjectAltName=" + san,
                    "-keyout", key, "-out", cert], check=True, capture_output=True)
    return cert, key


class Web:
    """The stand-in web: an HTTP proxy on 127.0.0.1 answering from PAGES."""

    def __init__(self):
        self.requests = []
        web = self

        class Handler(socketserver.StreamRequestHandler):
            def handle(self):
                line = self.rfile.readline().decode("latin-1").rstrip("\r\n")
                while self.rfile.readline() not in (b"\r\n", b"\n", b""):
                    pass
                web.requests.append(line)
                target = (line.split(" ") + ["", ""])[1]
                auth, _, path = target.removeprefix("http://").partition("/")
                status, headers, body = PAGES.get((auth, "/" + path.split("?")[0]), (404, {}, b"not found"))
                head = f"HTTP/1.1 {status} X\r\nConnection: close\r\n"
                if "Transfer-Encoding" not in headers and "Content-Length" not in headers:
                    head += f"Content-Length: {len(body)}\r\n"
                head += "".join(f"{k}: {v}\r\n" for k, v in headers.items())
                self.wfile.write(head.encode() + b"\r\n" + body)

        self.server = socketserver.ThreadingTCPServer(("127.0.0.1", 0), Handler)
        self.server.daemon_threads = True
        self.port = self.server.server_address[1]
        self.url = f"http://127.0.0.1:{self.port}"
        threading.Thread(target=self.server.serve_forever, args=(0.01,), daemon=True).start()


class GuardedFetch(unittest.TestCase):
    def setUp(self):
        self.web = Web()
        real, port, self.blocked = socket.getaddrinfo, self.web.port, []

        def only_the_proxy(host, p, *args, **kwargs):
            if host != "127.0.0.1" or str(p) != str(port):
                self.blocked.append(f"{host}:{p}")
                raise OSError("only the stand-in web is reachable")
            return real(host, p, *args, **kwargs)

        for patch in (mock.patch.object(socket, "getaddrinfo", only_the_proxy),
                      mock.patch.object(urllib.request, "proxy_bypass", lambda host: False)):
            patch.start()
            self.addCleanup(patch.stop)

    def tearDown(self):
        self.web.server.shutdown()
        self.web.server.server_close()
        self.assertEqual(self.blocked, [])

    def fetch(self, url, **kw):
        return gf.guarded_fetch(url, proxies={"http": self.web.url, "https": self.web.url}, pin=False,
                                **{**ALLOW, **kw})

    def test_an_allowed_url_is_fetched_exactly_as_checked(self):
        url = "http://docs.example.com/guide?v=3;a=//b"
        status, body, hops = self.fetch(url)
        self.assertEqual((status, body, len(hops)), (200, b"the guide", 1))
        self.assertEqual(self.web.requests, [f"GET {url} HTTP/1.1"])

    def test_the_default_opener_uses_the_environment_proxy_and_still_checks_redirects(self):
        with mock.patch.dict(os.environ, {"http_proxy": self.web.url}):
            with self.assertRaises(gf.Refused):
                gf.guarded_fetch("http://docs.example.com/leave302", pin=False, **ALLOW)
        self.assertEqual(self.web.requests, ["GET http://docs.example.com/leave302 HTTP/1.1"])

    def test_a_pinned_fetch_refuses_an_environment_proxy_before_sending_anything(self):
        with mock.patch.dict(os.environ, {"http_proxy": self.web.url}):
            with self.assertRaises(gf.Refused) as cm:
                gf.guarded_fetch("http://docs.example.com/guide", **ALLOW)
        self.assertIn("proxy", str(cm.exception))
        self.assertEqual(self.web.requests, [])
        with self.assertRaises(ValueError):
            gf.guarded_fetch("http://docs.example.com/guide", proxies={"http": self.web.url}, **ALLOW)

    def test_every_redirect_is_checked(self):
        status, _, hops = self.fetch("http://docs.example.com/moved")
        self.assertEqual((status, [h["url"] for h in hops]),
                         (200, ["http://docs.example.com/moved", "http://docs.example.com/guide"]))

    def test_a_redirect_to_another_host_is_refused_before_it_is_requested(self):
        cases = [(f"/leave{code}", "deny") for code in (301, 302, 303, 307, 308)] + [("/sneaky", "reject")]
        for path, decision in cases:
            with self.subTest(path=path):
                self.web.requests.clear()
                with self.assertRaises(gf.Refused) as cm:
                    self.fetch("http://docs.example.com" + path)
                self.assertEqual(cm.exception.hops[-1]["decision"], decision)
                self.assertEqual(self.web.requests, [f"GET http://docs.example.com{path} HTTP/1.1"])

    def test_refused_urls_are_never_requested(self):
        for url in ("http://docs.example.com.evil.example.net/", "http://docs.example.com@evil.example.net/",
                    "http://DOCS.example.com/guide", "http://127.1/", "https://docs.example.com/guide"):
            with self.subTest(url=url), self.assertRaises(gf.Refused):
                self.fetch(url)  # the last one is refused because only http is allowed here
        self.assertEqual(self.web.requests, [])

    def test_a_redirect_loop_stops(self):
        with self.assertRaises(gf.Refused):
            self.fetch("http://docs.example.com/loop", max_redirects=3)
        self.assertEqual(len(self.web.requests), 4)

    def test_a_broken_answer_refuses(self):
        with self.assertRaises(gf.Refused):
            self.fetch("http://docs.example.com/broken")

    def test_the_body_is_cut_at_max_bytes(self):
        status, body, _ = self.fetch("http://docs.example.com/large", max_bytes=1000)
        self.assertEqual((status, body), (200, b"z" * 1000))

    def test_a_body_shorter_than_its_content_length_refuses(self):
        for path in SHORT:
            with self.subTest(path=path):
                with self.assertRaises(gf.Refused) as cm:
                    self.fetch("http://docs.example.com" + path)
                self.assertIn("request failed", str(cm.exception))
        for kw in READ_ALL:
            with self.subTest(**kw):
                with self.assertRaises(gf.Refused):
                    self.fetch("http://docs.example.com/short", **kw)
        for path, kw, answer in NOT_SHORT:
            with self.subTest(path=path, **kw):
                self.assertEqual(self.fetch("http://docs.example.com" + path, **kw)[:2], answer)


class Origin:
    """The stand-in origin servers for pinned fetches: one TCP listener on 127.0.0.1 that records the
    first bytes of each connection, then answers an HTTP request from PAGES by its Host header (port
    removed) and path, or a TLS ClientHello with a fatal alert. With `cert` (certificate and key
    files), it completes TLS handshakes with that certificate instead, records the request that
    arrives over TLS and answers it from PAGES, then closes the connection without a TLS
    close_notify."""

    def __init__(self, cert=None):
        self.records = []
        origin = self
        context = None
        if cert is not None:
            context = ssl.SSLContext(ssl.PROTOCOL_TLS_SERVER)
            context.load_cert_chain(*cert)

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
                except OSError:  # ssl.SSLError included
                    pass
                origin.records.append(data)
                if data[:1] == b"\x16":
                    answer = compat.TLS_ALERT
                else:
                    lines = data.split(b"\r\n\r\n", 1)[0].decode("latin-1").split("\r\n")
                    path = (lines[0].split(" ") + ["", ""])[1].split("?")[0]
                    host = (compat.header(lines, "Host") or "").rsplit(":", 1)[0]
                    status, headers, body = PAGES.get((host, path), (404, {}, b"not found"))
                    head = f"HTTP/1.1 {status} X\r\nConnection: close\r\n"
                    if "Content-Length" not in headers:
                        head += f"Content-Length: {len(body)}\r\n"
                    head += "".join(f"{k}: {v}\r\n" for k, v in headers.items())
                    answer = head.encode() + b"\r\n" + body
                try:
                    conn.sendall(answer)
                except OSError:
                    pass
                if conn is not self.request:
                    conn.close()  # without unwrap(), so no close_notify: the TLS stream just ends

        self.server = socketserver.ThreadingTCPServer(("127.0.0.1", 0), Handler)
        self.server.daemon_threads = True
        self.port = self.server.server_address[1]
        threading.Thread(target=self.server.serve_forever, args=(0.01,), daemon=True).start()

    def close(self):
        self.server.shutdown()
        self.server.server_close()

    def heads(self):
        """The request line and Host header of each HTTP request so far."""
        out = []
        for data in self.records:
            lines = data.split(b"\r\n\r\n", 1)[0].decode("latin-1").split("\r\n")
            out.append((lines[0], compat.header(lines, "Host")))
        return out


class Pinned(unittest.TestCase):
    def setUp(self):
        self.origin = Origin()
        self.answers, self.lookups, self.connects = {}, [], []

        def getaddrinfo(host, port, *args, **kwargs):
            self.lookups.append((host, port))
            seq = self.answers.get(host)
            if not seq:
                raise socket.gaierror(socket.EAI_NONAME, "no such name here")
            addrs = seq.pop(0) if len(seq) > 1 else seq[0]
            out = []
            for a in addrs:
                if ":" in a:
                    addr, _, scope = a.partition("%")
                    out.append((socket.AF_INET6, socket.SOCK_STREAM, 6, "", (addr, port, 0, int(scope or 0))))
                else:
                    out.append((socket.AF_INET, socket.SOCK_STREAM, 6, "", (a, port)))
            return out

        def open_socket(addr, port):
            self.connects.append((addr, port))
            s = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
            s.settimeout(5)
            s.connect(("127.0.0.1", self.origin.port))  # numeric: no lookup
            return s

        for patch in (mock.patch.object(socket, "getaddrinfo", getaddrinfo),
                      mock.patch.object(gf, "open_socket", open_socket),
                      mock.patch.object(urllib.request, "getproxies", lambda: {})):
            patch.start()
            self.addCleanup(patch.stop)

    def tearDown(self):
        self.origin.close()

    def fetch(self, url, answers, **kw):
        self.answers.update({h: [list(a) for a in seq] for h, seq in answers.items()})
        return gf.guarded_fetch(url, **{**ALLOW, **kw})

    def test_a_checked_address_is_connected_to_and_the_host_is_kept(self):
        status, body, hops = self.fetch("http://docs.example.com/guide?v=3#top", {"docs.example.com": [["8.8.8.8"]]})
        self.assertEqual((status, body), (200, b"the guide"))
        self.assertEqual(self.connects, [("8.8.8.8", 80)])
        self.assertEqual(self.origin.heads(), [("GET /guide?v=3 HTTP/1.1", "docs.example.com")])
        self.assertEqual(hops[0]["addrs"], [{"addr": "8.8.8.8", "decision": "allow", "reason": None}])
        self.assertEqual(hops[0]["connected"], "8.8.8.8")

    def test_port_and_ipv6(self):
        self.fetch("http://docs.example.com:8080/guide", {"docs.example.com": [["2606:4700:4700::1111"]]})
        self.assertEqual(self.connects, [("2606:4700:4700::1111", 8080)])
        self.assertEqual(self.origin.heads(), [("GET /guide HTTP/1.1", "docs.example.com:8080")])

    def test_every_answer_is_checked_before_any_connection(self):
        cases = [
            (["127.0.0.1"], []), (["10.0.0.1"], []), (["169.254.169.254"], []), (["100.100.100.200"], []),
            (["192.0.0.192"], []), (["::1"], []), (["::ffff:127.0.0.1"], []), (["::ffff:a9fe:a9fe"], []),
            (["::127.0.0.1"], []), (["64:ff9b::a9fe:a9fe"], []), (["64:ff9b::a9fe:a9fe"], ["64:ff9b::/96"]),
            (["64:ff9b:1::a00:1"], []), (["2002:7f00:1::1"], []), (["2001:0:4136:e378:8000:63bf:3fff:fdd2"], []),
            (["2606:4700::5efe:a9fe:a9fe"], []), (["fd00:ec2::254"], []), (["fe80::1%2"], []), (["fec0::1"], []),
            (["8.8.8.8", "127.0.0.1"], []), (["127.0.0.1", "8.8.8.8"], []),
            (["2606:4700:4700::1111", "::ffff:169.254.169.254"], []),
        ]
        for addrs, nat64 in cases:
            with self.subTest(addrs=addrs, nat64=nat64):
                with self.assertRaises(gf.Refused) as cm:
                    self.fetch("http://docs.example.com/guide", {"docs.example.com": [addrs]}, nat64=nat64)
                self.assertTrue(any(a["decision"] != "allow" for a in cm.exception.hops[-1]["addrs"]))
        self.assertEqual((self.connects, self.origin.records), ([], []))

    def test_a_configured_nat64_prefix_decides_on_the_ipv4_address(self):
        status, _, hops = self.fetch("http://docs.example.com/guide", {"docs.example.com": [["64:ff9b::808:808"]]},
                                     nat64=["64:ff9b::/96"])
        self.assertEqual(status, 200)
        self.assertEqual(self.connects, [("64:ff9b::808:808", 80)])
        # A prefix nat64Ok would ignore is a usage error, and the fetch refuses.
        with self.assertRaises(gf.Refused):
            self.fetch("http://docs.example.com/guide", {"docs.example.com": [["64:ff9b:1::808:808"]]},
                       nat64=["64:ff9b:1::/96"])
        self.assertEqual(len(self.connects), 1)

    def test_deny_addr(self):
        with self.assertRaises(gf.Refused):
            self.fetch("http://docs.example.com/guide", {"docs.example.com": [["8.8.8.8"]]}, deny_addr=["8.8.0.0/16"])
        self.assertEqual(self.connects, [])

    def test_an_answer_that_changes_between_hops_is_checked_again(self):
        # Public on the first lookup, loopback on the second: the redirect is not followed.
        with self.assertRaises(gf.Refused) as cm:
            self.fetch("http://docs.example.com/moved", {"docs.example.com": [["8.8.8.8"], ["127.0.0.1"]]})
        hops = cm.exception.hops
        self.assertEqual([h["url"] for h in hops], ["http://docs.example.com/moved", "http://docs.example.com/guide"])
        self.assertEqual(hops[1]["addrs"][0]["decision"], "deny")
        self.assertEqual(self.connects, [("8.8.8.8", 80)])
        self.assertEqual(self.lookups, [("docs.example.com", 80), ("docs.example.com", 80)])

    def test_a_body_shorter_than_its_content_length_refuses(self):
        answers = {"docs.example.com": [["8.8.8.8"]]}
        for path in SHORT:
            with self.subTest(path=path):
                with self.assertRaises(gf.Refused) as cm:
                    self.fetch("http://docs.example.com" + path, answers)
                self.assertIn("request failed", str(cm.exception))
        for kw in READ_ALL:
            with self.subTest(**kw):
                with self.assertRaises(gf.Refused):
                    self.fetch("http://docs.example.com/short", answers, **kw)
        for path, kw, answer in NOT_SHORT:
            with self.subTest(path=path, **kw):
                self.assertEqual(self.fetch("http://docs.example.com" + path, answers, **kw)[:2], answer)

    def test_a_body_cut_short_over_https_refuses(self):
        # The origin ends the TLS connection without close_notify, as an injected FIN would.
        files = throwaway_cert(self, "DNS:docs.example.com")
        self.origin.close()
        self.origin = Origin(files)
        https = dict(schemes=("https",), context=ssl.create_default_context(cafile=files[0]))
        answers = {"docs.example.com": [["8.8.8.8"]]}
        self.assertEqual(self.fetch("https://docs.example.com/guide", answers, **https)[:2], (200, b"the guide"))
        with self.assertRaises(gf.Refused) as cm:
            self.fetch("https://docs.example.com/short", answers, **https)
        self.assertIn("request failed", str(cm.exception))

    def test_https_uses_the_url_host_as_server_name(self):
        with self.assertRaises(gf.Refused):  # the fixture ends the handshake with an alert
            self.fetch("https://docs.example.com/guide", {"docs.example.com": [["8.8.8.8"]]}, schemes=("https",))
        self.assertEqual(self.connects, [("8.8.8.8", 443)])
        self.assertEqual([compat.client_hello_names(r) for r in self.origin.records], [["docs.example.com"]])

    def test_an_ip_host_allowed_by_the_url_check_is_still_checked(self):
        with self.assertRaises(gf.Refused):
            self.fetch("http://127.0.0.1/guide", {"127.0.0.1": [["127.0.0.1"]]}, allow=["127.0.0.1"])
        self.assertEqual(self.connects, [])

    def test_no_lookup_for_a_refused_url_and_no_connection_without_an_answer(self):
        with self.assertRaises(gf.Refused):
            self.fetch("http://evil.example.net/", {"evil.example.net": [["8.8.8.8"]]})
        self.assertEqual(self.lookups, [])
        with self.assertRaises(gf.Refused):
            self.fetch("http://docs.example.com/guide", {})
        self.assertEqual(self.connects, [])

    def test_only_the_checked_address_is_connected_to(self):
        # An answer whose printed address is not the checked one refuses, before connecting.
        for addr in ("127.0.0.1", "8.8.4.4", "localhost", None):
            answer = [{"input": "8.8.8.8", "decision": "allow", "family": "ipv4", "addr": addr}]
            with self.subTest(addr=addr), mock.patch.object(gf, "check_addrs", return_value=(answer, None)):
                with self.assertRaises(gf.Refused):
                    self.fetch("http://docs.example.com/guide", {"docs.example.com": [["8.8.8.8"]]})
        self.assertEqual(self.connects, [])

    def test_unusable_address_answers_refuse(self):
        def says(code, out):
            return mock.patch.object(gf.subprocess, "run",
                                     return_value=subprocess.CompletedProcess([], code, out, b""))
        good = b'{"input":"8.8.8.8","decision":"allow"}\n'
        for code, out in ((1, good), (0, b'{"input":"8.8.4.4","decision":"allow"}\n'), (0, b""), (0, good + good),
                          (0, b"[]\n"), (2, b"")):
            with self.subTest(code=code, out=out), says(code, out):
                self.assertEqual(gf.check_addrs(["8.8.8.8"])[0], None)
        with self.assertRaises(TypeError):
            gf.check_addrs(["8.8.8.8"], deny="10.0.0.0/8")


class RealOpenSocket(unittest.TestCase):
    """The example's own `open_socket`, against a listener on 127.0.0.1: it connects to a numeric
    address and refuses anything else without a lookup."""

    def test_numeric_only(self):
        listener = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        self.addCleanup(listener.close)
        listener.bind(("127.0.0.1", 0))
        listener.listen(5)
        listener.settimeout(0.5)
        port = listener.getsockname()[1]
        lookups = []

        def no_lookup(host, *args, **kwargs):
            lookups.append(host)
            raise OSError("no lookup allowed here")

        with mock.patch.object(socket, "getaddrinfo", no_lookup):
            s = gf.open_socket("127.0.0.1", port)
            s.close()
            conn, _ = listener.accept()
            conn.close()
            for bad in ("localhost", "127.1", "0x7f.0.0.1", "fe80::1%lo", "", "127.0.0.1 "):
                with self.subTest(addr=bad), self.assertRaises(ValueError):
                    gf.open_socket(bad, port)
        self.assertEqual(lookups, [])
        with self.assertRaises(socket.timeout):
            listener.accept()  # nothing else connected


class Confinement(unittest.TestCase):
    """tests/common.py's guard, through the code paths the tests use: a connection to 192.0.2.1
    (TEST-NET-1), plain or for TLS, made by the example, http.client, urllib or ssl, and a lookup of a
    name, are refused with Outbound before they are made."""

    def setUp(self):
        # A connect to 0.0.0.0 would reach this listener on 127.0.0.1. It is refused and nothing
        # arrives, so the guard is in place, and stops a connect before it is made, before anything
        # below tries 192.0.2.1.
        listener = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        self.addCleanup(listener.close)
        listener.bind(("127.0.0.1", 0))
        listener.listen(5)
        listener.settimeout(0.2)
        probe = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        self.addCleanup(probe.close)
        self.refused(lambda: probe.connect(("0.0.0.0", listener.getsockname()[1])), "0.0.0.0")
        with self.assertRaises(socket.timeout):
            listener.accept()
        patch = mock.patch.object(urllib.request, "getproxies", lambda: {})
        patch.start()
        self.addCleanup(patch.stop)

    def refused(self, attempt, target):
        before = len(common.OUTBOUND)
        with self.assertRaises(common.Outbound):
            attempt()
        new = common.OUTBOUND[before:]
        self.assertEqual(len(new), 1, new)
        self.assertIn(target, repr(new[0][1]))

    def test_plain(self):
        opener = urllib.request.build_opener(urllib.request.ProxyHandler({}))
        self.refused(lambda: gf.open_socket("192.0.2.1", 80), "192.0.2.1")
        self.refused(lambda: http.client.HTTPConnection("192.0.2.1", 80, timeout=1).request("GET", "/"), "192.0.2.1")
        self.refused(lambda: opener.open("http://192.0.2.1/", timeout=1), "192.0.2.1")
        self.refused(lambda: gf.guarded_fetch("http://192.0.2.1/", allow=["192.0.2.1"], schemes=("http",), pin=False,
                                              proxies={}), "192.0.2.1")

    def test_tls(self):
        context = ssl.create_default_context()
        opener = urllib.request.build_opener(urllib.request.ProxyHandler({}))
        tls = context.wrap_socket(socket.socket(socket.AF_INET, socket.SOCK_STREAM), server_hostname="docs.example.com")
        self.addCleanup(tls.close)
        self.refused(lambda: gf.PinnedHTTPSConnection("docs.example.com", 443, "192.0.2.1", context).connect(),
                     "192.0.2.1")
        self.refused(lambda: tls.connect(("192.0.2.1", 443)), "192.0.2.1")
        self.refused(lambda: http.client.HTTPSConnection("192.0.2.1", 443, timeout=1, context=context).request("GET", "/"),
                     "192.0.2.1")
        self.refused(lambda: opener.open("https://192.0.2.1/", timeout=1), "192.0.2.1")

    def test_names_are_not_looked_up(self):
        # As if a test forgot to replace getaddrinfo: the lookup itself is refused, here also for a
        # pinned fetch, which resolves the host with getaddrinfo. The name is under .invalid, so
        # that not even a broken guard could make a real lookup of it.
        name = "docs.example.invalid"
        plain = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        self.addCleanup(plain.close)
        self.refused(lambda: socket.getaddrinfo(name, 443), name)
        self.refused(lambda: socket.gethostbyname(name), name)
        self.refused(lambda: plain.connect((name, 80)), name)
        self.refused(lambda: gf.guarded_fetch(f"http://{name}/guide", allow=[name], schemes=("http",)), name)


def urlfence_says(code, stdout, stderr=b""):
    return mock.patch.object(gf.subprocess, "run",
                             return_value=subprocess.CompletedProcess([], code, stdout, stderr))


class UnusableAnswers(unittest.TestCase):
    URL = "http://docs.example.com/guide"

    def test_each_refuses(self):
        good = b'{"input":"%s","decision":"allow"}\n' % self.URL.encode()
        for code, out in ((0, b'{"input":"http://docs.example.com/other","decision":"allow"}\n'),
                          (1, good), (3, good), (0, b"not json\n"), (0, b"[]\n"), (0, b""), (0, good + good)):
            with self.subTest(code=code, out=out), urlfence_says(code, out):
                self.assertEqual(gf.check(self.URL, **ALLOW)["decision"], "reject")

    def test_a_usage_error_refuses_and_says_why(self):
        with urlfence_says(2, b"", b"urlfence: invalid pattern\n"):
            r = gf.check(self.URL, **ALLOW)
        self.assertEqual((r["decision"], r["reason"]), ("reject", "urlfence: urlfence: invalid pattern"))

    def test_a_timeout_is_set_and_refuses(self):
        with mock.patch.object(gf.subprocess, "run", side_effect=subprocess.TimeoutExpired("urlfence", 1)) as run:
            self.assertEqual(gf.check(self.URL, **ALLOW)["decision"], "reject")
        self.assertEqual(run.call_args.kwargs["timeout"], gf.TIMEOUT)

    def test_input_the_binary_cannot_take_refuses(self):
        for bad in ("http://docs.example.com/a\x00b", "http://docs.example.com/\ud800", None):
            with self.subTest(arg=repr(bad)):
                self.assertEqual(gf.check(bad, **ALLOW)["decision"], "reject")

    def test_a_single_string_policy_is_an_error(self):
        with self.assertRaises(TypeError):
            gf.check(self.URL, allow="docs.example.com", schemes=("http",))


if __name__ == "__main__":
    unittest.main()
