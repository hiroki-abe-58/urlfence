"""`examples/guarded_fetch.py` end to end: the real `urlfence` binary, and an HTTP proxy on 127.0.0.1
that stands in for the web (it serves a few pages and records every request), so nothing leaves the
machine. While a test runs, any `getaddrinfo` lookup other than the proxy's is refused. Unusable
answers from the binary are simulated by replacing `subprocess.run`."""
import os
import socket
import socketserver
import subprocess
import sys
import threading
import unittest
import urllib.request
from unittest import mock

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
}
for code in (301, 302, 303, 307, 308):
    PAGES[("docs.example.com", f"/leave{code}")] = (code, {"Location": "http://evil.example.net/collect"}, b"")
ALLOW = dict(allow=["docs.example.com"], schemes=("http",))


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
                if "Transfer-Encoding" not in headers:
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
        return gf.guarded_fetch(url, proxies={"http": self.web.url, "https": self.web.url}, **{**ALLOW, **kw})

    def test_an_allowed_url_is_fetched_exactly_as_checked(self):
        url = "http://docs.example.com/guide?v=3;a=//b"
        status, body, hops = self.fetch(url)
        self.assertEqual((status, body, len(hops)), (200, b"the guide", 1))
        self.assertEqual(self.web.requests, [f"GET {url} HTTP/1.1"])

    def test_the_default_opener_uses_the_environment_proxy_and_still_checks_redirects(self):
        with mock.patch.dict(os.environ, {"http_proxy": self.web.url}):
            with self.assertRaises(gf.Refused):
                gf.guarded_fetch("http://docs.example.com/leave302", **ALLOW)
        self.assertEqual(self.web.requests, ["GET http://docs.example.com/leave302 HTTP/1.1"])

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
