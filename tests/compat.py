"""Client compatibility: do HTTP clients read every URL that URLFence accepts the same way?

For each URL that URLFence accepts (decision `allow` or `deny`), each client must agree with
URLFence's scheme, host and port (`:80`/`:443` count as the default) and see no userinfo. There are
three kinds of observation, reported separately:

* parser: what the client's URL parser reports. No network.
* request: what the client actually asks for, observed by a local HTTP proxy fixture on 127.0.0.1.
  The fixture answers 403 and closes the connection. curl is always given the fixture as its
  proxy; while the Python clients run, any address lookup other than for the fixture's address and
  port is refused and fails the run. So nothing leaves this machine.
  * For an http URL the client sends the absolute URL and a `Host` header; credentials it takes
    from the URL show up in the request line or in an `Authorization` header.
  * For an https URL the client sends only `CONNECT host:port`: the userinfo, the TLS server name
    and the inner `Host` header would travel inside the tunnel, which the fixture never opens.
  This exercises the proxy path only, and there is no proxy view for Node's http module.
* direct: what the client does on its direct path (no proxy). Each connection the client opens is
  intercepted, its target recorded, and sent to a fixture on 127.0.0.1, which records what arrives
  first (an HTTP request head, or a TLS ClientHello), answers 403 or a fatal TLS alert, and
  closes. The client must connect to URLFence's host and effective port, and then:
  * for http, send an origin-form request (`GET /...`) whose `Host` header names that host and
    port, and no `Authorization` header (credentials taken from the URL);
  * for https, send that host as the TLS server name (SNI, parsed from the ClientHello). For an
    IPv4 host, no server name (RFC 6066 forbids an address there) or the address itself.
  How the target is intercepted, per client:
  * node: `http.request(url)` or `https.request(url)` (tests/compat_direct.js) with an Agent whose
    `createConnection` records the host and port Node derived, then connects to the fixture with
    every other option, the server name included, as Node computed it. `dns.lookup` and
    `net.Socket.prototype.connect` refuse, and fail the run on, anything but the fixture.
  * urllib.request (through http.client), urllib3 and requests: inside each call of
    `socket.create_connection` (http.client) or urllib3's own `create_connection` (urllib3,
    requests), the one address lookup the client makes is answered with the fixture's address and
    recorded as the client's target; the rest of the client's code runs unchanged. Any other
    lookup is refused and fails the run, as for the request views. `ssl.SSLContext.wrap_socket`
    records the `server_hostname`, the name the client checks the certificate against, which must
    be the host whenever one is given (urllib3 gives none for an IP address; it then checks the
    certificate itself after the handshake, which never completes here).
  * curl: four `--connect-to` rules, tried in order, send the connection to one of four fixture
    ports depending on whether curl's own connection host and port (what it would resolve and
    connect to) equal URLFence's host and port (curl compares hosts ignoring ASCII case). So a difference names which of the two differs,
    not curl's value; the `Host` header and the server name show curl's host as sent.
  Not observed: DNS (nothing is resolved, so what an allowed name resolves to, and how the system
  resolver would read the name, are out of scope), whether the certificate is verified, and
  everything inside TLS (the inner request, its `Host` header and any
  credentials), since the handshake never completes; and anything after the first message.
  To keep the run short, urllib3 and requests are given the system CA directory instead of a CA
  bundle file, and curl `--insecure`: either way only the loading of CA certificates before each
  handshake is skipped, not anything the client sends.

A client that is not installed, or lacks what a view needs, is reported as SKIPPED and is never
counted as agreeing; `--require` turns a skip into a failure. A disagreement always fails the run.
A client that refuses an accepted URL (raises, or sends nothing) is listed as `refused`: it went
nowhere, so it is not a disagreement, but `--strict` makes it fail too, and so does a view that
refuses more than 1% of the URLs (that view is broken, not cautious).

The corpus is deterministic (fixed lists plus a seeded generator with its own PRNG); its size and
SHA-256 are pinned below, and the first 16 hex digits are printed (all of it with `--json`).
`--quick` uses a fixed 1/16 subset. `--self-test` checks that every view reports a difference for
each of a few deliberately wrong expectations (host and port over http and https, userinfo over
http), except where what a client sends has nothing to show (it refuses the URL, or drops the
userinfo); those cases, and what the client does instead, are listed in SELF_TEST_UNSEEN and must
happen exactly so.

    python3 tests/compat.py                 # the full corpus
    python3 tests/compat.py --self-test     # then, as CI runs it:
    python3 tests/compat.py --quick --strict --require whatwg,node,urlsplit,urllib.request,curl
"""
import argparse
import base64
import collections
import hashlib
import json
import os
import platform
import shutil
import socket
import socketserver
import ssl
import subprocess
import sys
import threading

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from common import NODE, is_ipv4, run_check, whatwg  # noqa: E402

DEFAULT_PORT = {"http": 80, "https": 443}
CORPUS_SIZE = 41647
CORPUS_SHA256 = "53c3e079725394e66aa0efb73aec413e4e98257b5e9a8820a3cb29a8882d2241"

# ---- the corpus ----------------------------------------------------------------------------------


class SplitMix64:
    """A small PRNG with a fixed definition, so the corpus does not depend on Python's `random`."""

    MASK = (1 << 64) - 1

    def __init__(self, seed):
        self.state = seed & self.MASK

    def next(self):
        self.state = (self.state + 0x9E3779B97F4A7C15) & self.MASK
        z = self.state
        z = ((z ^ (z >> 30)) * 0xBF58476D1CE4E5B9) & self.MASK
        z = ((z ^ (z >> 27)) * 0x94D049BB133111EB) & self.MASK
        return z ^ (z >> 31)

    def below(self, n):
        return self.next() % n

    def choice(self, xs):
        return xs[self.below(len(xs))]


PRINTABLE = [chr(c) for c in range(0x21, 0x7f)]
HOSTS = [
    "example.com", "a.b.example.com", "localhost", "a", "x", "com", "1.com", "0x7f.com", "0.0.0.com",
    "1.2.3.com", "0x.com", "255.255.255.a", "1.2.3.4a", "1.2.3.a4", "0xg", "a.0xg", "a.0b1", "a.0o7",
    "a.1e5", "a.1a", "a.08x", "a.x0", "0x1g.com", "a-b.com", "a--b.com", "ab--cd.com", "1-1.com",
    "xn--bcher-kva.example", "xn--ls8h.la", "xn--zca.com", "xn--a.com", "xn--0ga.com", "0.0.0.0",
    "255.255.255.255", "127.0.0.1", "1.2.3.4", "249.250.251.252", "199.200.201.255", "10.0.0.1",
    "a" * 63 + ".com", "a" * 63 + "." + "b" * 63 + "." + "c" * 63 + "." + "d" * 61,
    "a" * 63 + "." + "b" * 63 + "." + "c" * 63 + "." + "d" * 62, "a" * 64 + ".com",
    "0-0.0-0", "9.9.9.9x", "ff", "0xffg.0xff.com", "xn--.com", "a.b.c.d.e.f.g.h", "q" * 10,
    "1.2.3.4.5", "01.2.3.4", "1.2.3.04", "256.1.1.1", "1.2.3.255", "0.1.2.3",
]
PORTS = ["", ":0", ":1", ":80", ":443", ":8080", ":65535", ":9", ":65536", ":00", ":1a"]
SMALL_RESTS = ["", "/", "/x?y#z", "?", "#", "?@evil.com", "#@evil.com", "/@evil.com"]
# Look-alikes and invisible characters next to the authority; all must be refused.
UNICODE = ["\t", " ", "　", "。", "．", "⁄", "：", "＠", "­"]


def corpus():
    rests = set(SMALL_RESTS)
    for c in PRINTABLE:
        for t in ["/" + c, "?" + c, "#" + c, "/" + c + "@evil.com", "?" + c + "@evil.com/", "#" + c + ".evil.com",
                  "/" + c + "/evil.com", "?" + c + "//evil.com", "/x" + c + "y"]:
            rests.add(t)
    rests |= {"//evil.com", "/..//evil.com", "/%2e%2e/", "/;@evil.com", "?a=1#b", "/a;b=c", "//@evil.com",
              "/.;/x", "?%40evil.com", "#%2F%2Fevil.com", "/é"}
    rests = sorted(rests)
    urls = set()
    for h in HOSTS:
        for p in PORTS:
            for r in SMALL_RESTS:
                for s in ["https://", "http://"]:
                    urls.add(s + h + p + r)
    for h in ["example.com", "1.2.3.4", "a.b.example.com", "xn--bcher-kva.example", "localhost"]:
        for p in ["", ":8443", ":443"]:
            for r in rests:
                urls.add("https://" + h + p + r)
    # Characters right after or before the host or port: the authority boundary.
    for h in ["example.com", "1.2.3.4"]:
        for c in PRINTABLE + UNICODE:
            for t in [c, c + "evil.com", c + "@evil.com", ":1" + c, c + ":1", ".evil.com" + c]:
                urls.add("https://" + h + t + "/")
            urls.add("https://" + c + h + "/")
    rng = SplitMix64(20261028)
    alpha = "abcxyz0189-.:/?#@;%[]\\"
    for _ in range(20000):
        urls.add("https://" + "".join(rng.choice(alpha) for _ in range(1 + rng.below(14))))
    return sorted(urls)


def digest(urls):
    return hashlib.sha256("".join(u + "\n" for u in urls).encode("utf-8")).hexdigest()


# ---- comparison ----------------------------------------------------------------------------------


class View:
    """One client seen one way (parser, request or direct): counts and the first few examples."""

    def __init__(self, client, kind):
        self.client, self.kind = client, kind
        self.version, self.status = "-", "ran"
        self.agree, self.refused, self.differs = 0, [], []
        self.outcome = {}  # url -> "agree", "refused" or "differs", for the self-test
        self.blocked = []  # lookups or connections a client tried beyond the fixture (node direct)

    def skip(self, why, status="SKIPPED"):
        self.status = f"{status}: {why}"
        return self

    @property
    def ran(self):
        return self.status == "ran"

    def record_all(self, urls, expected, got):
        """`got[i]` is (scheme, host, port, userinfo), something else that names a difference, or
        None for a refusal."""
        if not self.ran:
            return
        if len(got) != len(urls):
            raise RuntimeError(f"{self.client} {self.kind}: {len(got)} results for {len(urls)} URLs")
        for url, e, g in zip(urls, expected, got):
            if g is None:
                self.refused.append(url)
                self.outcome[url] = "refused"
            elif g != e:
                self.differs.append((url, g))
                self.outcome[url] = "differs"
            else:
                self.agree += 1
                self.outcome[url] = "agree"


def expected_of(r):
    scheme = r["scheme"]
    return (scheme, r["host"], int(r["port"]) if r["port"] else DEFAULT_PORT[scheme], "")


def eff_port(port, scheme):
    return int(port) if port not in (None, "") else DEFAULT_PORT.get(scheme)


def split_hostport(hp):
    host, sep, port = hp.rpartition(":")
    if sep and port.isascii() and port.isdigit():
        return host, int(port)
    return hp, None


# ---- parser views --------------------------------------------------------------------------------


def parse_whatwg(urls, view):
    if NODE is None:
        return view.skip("node is not installed")
    view.version = "node " + subprocess.run([NODE, "--version"], capture_output=True, text=True).stdout.strip()
    out = []
    for w in whatwg(urls):
        if not w["ok"]:
            out.append(None)
            continue
        scheme = w["protocol"].rstrip(":")
        out.append((scheme, w["hostname"], eff_port(w["port"], scheme), w["username"] + w["password"]))
    return out


def parse_urlsplit(urls, view):
    import urllib.parse
    view.version = "Python " + platform.python_version()
    out = []
    for u in urls:
        try:
            s = urllib.parse.urlsplit(u)
            out.append((s.scheme, s.hostname, eff_port(s.port, s.scheme), (s.username or "") + (s.password or "")))
        except ValueError:
            out.append(None)
    return out


def parse_urllib_request(urls, view):
    import urllib.request
    view.version = "Python " + platform.python_version()
    out = []
    for u in urls:
        try:
            r = urllib.request.Request(u)
            user, _, hostport = r.host.rpartition("@")
            host, port = split_hostport(hostport)
            out.append((r.type, host, eff_port(port, r.type), user))
        except ValueError:
            out.append(None)
    return out


def parse_urllib3(urls, view):
    try:
        import urllib3
    except ImportError:
        return view.skip("urllib3 is not installed")
    view.version = "urllib3 " + urllib3.__version__
    out = []
    for u in urls:
        try:
            p = urllib3.util.parse_url(u)
            out.append((p.scheme, p.host, eff_port(p.port, p.scheme), p.auth or ""))
        except ValueError:  # LocationParseError and LocationValueError are ValueErrors
            out.append(None)
    return out


def parse_requests(urls, view):
    """requests prepares the URL (its own normalisation), and urllib3 then parses the result."""
    try:
        import requests
        import urllib3
    except ImportError:
        return view.skip("requests is not installed")
    view.version = f"requests {requests.__version__} (urllib3 {urllib3.__version__})"
    out = []
    for u in urls:
        try:
            pr = requests.models.PreparedRequest()
            pr.prepare_url(u, None)
            p = urllib3.util.parse_url(pr.url)
            out.append((p.scheme, p.host, eff_port(p.port, p.scheme), p.auth or ""))
        except ValueError:  # InvalidURL, MissingSchema, InvalidSchema and urllib3's errors are ValueErrors
            out.append(None)
    return out


# ---- the proxy fixture and request views ----------------------------------------------------------


class Fixture:
    """An HTTP proxy on 127.0.0.1 that records each request head, answers 403 and closes."""

    def __init__(self):
        self.records, self.lock = [], threading.Lock()
        fixture = self

        class Handler(socketserver.StreamRequestHandler):
            def handle(self):
                self.request.settimeout(5)
                data = b""
                try:
                    while b"\r\n\r\n" not in data and len(data) < 65536:
                        chunk = self.request.recv(4096)
                        if not chunk:
                            break
                        data += chunk
                except OSError:
                    pass
                lines = data.split(b"\r\n\r\n", 1)[0].decode("latin-1").split("\r\n")
                with fixture.lock:  # recorded before the answer, so the client cannot finish first
                    fixture.records.append(lines)
                try:
                    self.request.sendall(b"HTTP/1.1 403 Forbidden\r\nContent-Length: 0\r\nConnection: close\r\n\r\n")
                except OSError:
                    pass

        self.server = socketserver.ThreadingTCPServer(("127.0.0.1", 0), Handler)
        self.server.daemon_threads = True
        self.url = f"http://127.0.0.1:{self.server.server_address[1]}"
        threading.Thread(target=self.server.serve_forever, daemon=True).start()

    def take(self):
        with self.lock:
            r, self.records = self.records, []
        return r

    def close(self):
        self.server.shutdown()
        self.server.server_close()


class FixtureOnly:
    """While active, refuse (and count) any address lookup in this process other than for a
    fixture's address and port. Every connection the Python clients make starts with
    `getaddrinfo`, IP literals included."""

    def __init__(self, ports):
        self.ports, self.blocked = {str(p) for p in ports}, []

    def __enter__(self):
        self.real = socket.getaddrinfo

        def guarded(host, port, *args, **kwargs):
            if host not in ("127.0.0.1", b"127.0.0.1") or str(port) not in self.ports:
                self.blocked.append(f"{host}:{port}")
                raise OSError(f"compat.py: refusing to resolve {host!r} port {port!r}: only the fixture")
            return self.real(host, port, *args, **kwargs)

        socket.getaddrinfo = guarded
        return self

    def __exit__(self, *exc):
        socket.getaddrinfo = self.real


def header(lines, name):
    for l in lines[1:]:
        k, _, v = l.partition(":")
        if k.strip().lower() == name.lower():
            return v.strip()
    return None


def target_of(lines):
    """Where the client asked the proxy to go, as (scheme, host, port, userinfo), or a tuple that
    names what is wrong with the request."""
    parts = lines[0].split(" ")
    if len(parts) != 3:
        return ("unreadable request", lines[0])
    method, target, _ = parts
    if method == "CONNECT":
        host, port = split_hostport(target)
        scheme, user = "https", ""  # CONNECT cannot show userinfo (see the module docstring)
    elif target.startswith("http://"):
        auth = target[len("http://"):]
        for d in "/?#":
            auth = auth.split(d, 1)[0]
        scheme = "http"
        user, _, hp = auth.rpartition("@")
        host, port = split_hostport(hp)
        if header(lines, "Authorization") is not None:  # requests and curl move URL credentials here
            user = user or "(Authorization header)"
    else:
        return ("not a proxy request", lines[0])
    got = (scheme, host, eff_port(port, scheme), user)
    # The Host header must name the same place as the request target.
    h = header(lines, "Host")
    if h is not None:
        hh, hport = split_hostport(h)
        if (hh, eff_port(hport, scheme)) != (host, got[2]):
            return (scheme, f"{host} (Host: {h})", got[2], user)
    return got


def one_request(fixture, send):
    fixture.take()
    try:
        send()
    except Exception:  # every client fails on the 403; that is expected
        pass
    recs = fixture.take()
    if not recs:
        return None
    if len(recs) > 1:
        return ("several requests",) + tuple(str(target_of(r)) for r in recs)
    return target_of(recs[0])


def request_urllib(urls, fixture, view):
    import urllib.request
    view.version = "Python " + platform.python_version()
    # Without this, urllib consults the macOS or Windows proxy exceptions and may connect directly.
    urllib.request.proxy_bypass = lambda host: False
    opener = urllib.request.build_opener(urllib.request.ProxyHandler({"http": fixture.url, "https": fixture.url}))
    return [one_request(fixture, lambda u=u: opener.open(u, timeout=5)) for u in urls]


def request_urllib3(urls, fixture, view):
    try:
        import urllib3
    except ImportError:
        return view.skip("urllib3 is not installed")
    view.version = "urllib3 " + urllib3.__version__
    pm = urllib3.ProxyManager(fixture.url, retries=False, timeout=5)
    return [one_request(fixture, lambda u=u: pm.request("GET", u, retries=False, redirect=False)) for u in urls]


def request_requests(urls, fixture, view):
    try:
        import requests
    except ImportError:
        return view.skip("requests is not installed")
    view.version = "requests " + requests.__version__
    s = requests.Session()
    s.trust_env = False
    proxies = {"http": fixture.url, "https": fixture.url}
    return [one_request(fixture, lambda u=u: s.get(u, proxies=proxies, timeout=5, allow_redirects=False))
            for u in urls]


def curl_quote(s):
    return '"' + s.replace("\\", "\\\\").replace('"', '\\"') + '"'


def run_curl(urls, fixture, parser_view, request_view):
    """One curl run per chunk: `%{url.*}` gives curl's parse; the fixture sees the request.
    Every URL carries an `X-Compat-Id` header so that requests can be matched to URLs. curl has no
    system proxy exceptions; with no proxy variables and no curlrc (-q) it always uses the fixture."""
    curl = shutil.which("curl")
    if curl is None:
        parser_view.skip("curl is not installed")
        request_view.skip("curl is not installed")
        return None, None
    version = subprocess.run([curl, "--version"], capture_output=True, text=True).stdout.split("\n")[0].split(" ")[1]
    parser_view.version = request_view.version = "curl " + version
    env = {"PATH": os.environ.get("PATH", "/usr/bin:/bin")}
    parsed, requested = {}, {}
    for start in range(0, len(urls), 500):
        chunk = list(enumerate(urls[start:start + 500], start))
        blocks = []
        for i, u in chunk:
            blocks.append("\n".join([
                f"url = {curl_quote(u)}", f"proxy = {curl_quote(fixture.url)}",
                f'proxy-header = "X-Compat-Id: {i}"', f'header = "X-Compat-Id: {i}"', 'output = "/dev/null"',
                f'write-out = "{i}\\t%{{url.scheme}}\\t%{{url.host}}\\t%{{url.port}}\\t%{{url.user}}%{{url.password}}\\n"',
                # `next` resets per-URL options, so these are repeated in every block.
                "globoff", "silent", "max-time = 5"]))
        fixture.take()
        p = subprocess.run([curl, "-q", "-g", "-s", "-K", "-"], input="\nnext\n".join(blocks).encode(),
                           capture_output=True, env=env, timeout=600)
        for line in p.stdout.decode("utf-8", "replace").split("\n"):
            f = line.split("\t")
            if len(f) == 5 and f[0].isdigit():
                # curl prints the line with empty fields for a URL it refuses.
                parsed[int(f[0])] = (f[1], f[2], eff_port(f[3], f[1]), f[4]) if f[1] and f[2] else None
        for rec in fixture.take():
            i = header(rec, "X-Compat-Id")
            if i is not None and i.isdigit():
                requested.setdefault(int(i), []).append(rec)
    if not any(parsed.values()):  # an older curl prints nothing for an unknown %{url.*}
        parser_view.skip("this curl does not support %{url.*} in --write-out")
        parsed = None
    else:
        parsed = [parsed.get(i) for i in range(len(urls))]
    out = []
    for i in range(len(urls)):
        recs = requested.get(i, [])
        out.append(None if not recs else target_of(recs[0]) if len(recs) == 1 else ("several requests",))
    return parsed, out


# ---- the direct fixture and direct views ----------------------------------------------------------

TLS_ALERT = bytes([0x15, 0x03, 0x03, 0x00, 0x02, 0x02, 0x28])  # fatal handshake_failure
HTTP_403 = b"HTTP/1.1 403 Forbidden\r\nContent-Length: 0\r\nConnection: close\r\n\r\n"


def message_complete(data):
    """An HTTP head ends with an empty line; a TLS ClientHello is complete when its handshake
    records hold the whole message. (tests/compat_direct.js has the same rule.)"""
    if data[:1] != b"\x16":
        return b"\r\n\r\n" in data
    hs, pos = b"", 0
    while pos + 5 <= len(data):
        if data[pos] != 0x16:
            return True  # not a handshake record: stop, and let client_hello_names() say so
        n = int.from_bytes(data[pos + 3:pos + 5], "big")
        if pos + 5 + n > len(data):
            return False
        hs += data[pos + 5:pos + 5 + n]
        pos += 5 + n
        if len(hs) >= 4 and len(hs) >= 4 + int.from_bytes(hs[1:4], "big"):
            return True
    return False


def client_hello_names(data):
    """The host names in the server_name extension (SNI) of the TLS ClientHello that `data` starts
    with: [] if there is none. Raises ValueError or IndexError if it is not a whole ClientHello."""
    hs, pos = b"", 0
    while pos + 5 <= len(data) and data[pos] == 0x16:
        n = int.from_bytes(data[pos + 3:pos + 5], "big")
        hs += data[pos + 5:pos + 5 + n]
        pos += 5 + n
    if len(hs) < 4 or hs[0] != 1:
        raise ValueError("not a ClientHello")
    n = int.from_bytes(hs[1:4], "big")
    body = hs[4:4 + n]
    if len(body) != n:
        raise ValueError("truncated ClientHello")
    p = 34                                                  # legacy_version, random
    p += 1 + body[p]                                        # legacy_session_id
    p += 2 + int.from_bytes(body[p:p + 2], "big")           # cipher_suites
    p += 1 + body[p]                                        # legacy_compression_methods
    if p == len(body):
        return []                                           # no extensions
    end = p + 2 + int.from_bytes(body[p:p + 2], "big")
    if end != len(body):
        raise ValueError("bad extensions length")
    p += 2
    names = []
    while p < end:
        kind, n = int.from_bytes(body[p:p + 2], "big"), int.from_bytes(body[p + 2:p + 4], "big")
        ext, p = body[p + 4:p + 4 + n], p + 4 + n
        if p > end:
            raise ValueError("bad extension length")
        if kind != 0:                                       # server_name
            continue
        if 2 + int.from_bytes(ext[:2], "big") != len(ext):
            raise ValueError("bad server_name list length")
        q = 2
        while q < len(ext):
            name_type, m = ext[q], int.from_bytes(ext[q + 1:q + 3], "big")
            if q + 3 + m > len(ext):
                raise ValueError("bad server name length")
            if name_type == 0:                              # host_name
                names.append(ext[q + 3:q + 3 + m].decode("latin-1"))
            q += 3 + m
    return names


class DirectFixture:
    """Stands in for every server on the clients' direct paths: TCP listeners on 127.0.0.1 that
    record what each connection brings first (an HTTP request head or a TLS ClientHello), as
    (listening port, client port, bytes), then answer 403 or a fatal TLS alert, and close."""

    def __init__(self, listeners):
        self.records, self.cond = [], threading.Condition()
        fixture = self

        class Handler(socketserver.BaseRequestHandler):
            def handle(self):
                self.request.settimeout(5)
                data = b""
                try:
                    while len(data) < 65536 and not message_complete(data):
                        chunk = self.request.recv(4096)
                        if not chunk:
                            break
                        data += chunk
                except OSError:
                    pass
                with fixture.cond:  # recorded before the answer, so the client cannot finish first
                    fixture.records.append((self.server.server_address[1], self.client_address[1], data))
                    fixture.cond.notify_all()
                try:
                    self.request.sendall(TLS_ALERT if data[:1] == b"\x16" else HTTP_403)
                except OSError:
                    pass

        self.servers = []
        for _ in range(listeners):
            server = socketserver.ThreadingTCPServer(("127.0.0.1", 0), Handler)
            server.daemon_threads = True
            threading.Thread(target=server.serve_forever, daemon=True).start()
            self.servers.append(server)
        self.ports = [s.server_address[1] for s in self.servers]

    def take(self, n=0):
        """The records so far, once there are at least `n` of them (or after 5 seconds)."""
        with self.cond:
            self.cond.wait_for(lambda: len(self.records) >= n, timeout=5)
            r, self.records = self.records, []
        return r

    def close(self):
        for s in self.servers:
            s.shutdown()
            s.server_close()


def direct_of(connects, recs, names=None):
    """What a client did on its direct path, as (scheme, host, port, userinfo), or a tuple that names
    what is wrong. `connects` holds the (host, port) of each connection the client opened, `recs`
    what the fixture received on each, and `names` (Python clients) the `server_hostname` of each
    TLS wrap. Each observation is compared with the connection's own host and port; what differs is
    appended to the host, so that the result equals URLFence's reading only if everything agrees."""
    if not connects and not recs:
        return None
    if len(connects) != 1 or len(recs) != 1:
        return ("several connections" if len(connects) > 1 else "connections and fixture records differ",
                str(connects), len(recs))
    (host, port), data = connects[0], recs[0]
    notes, user = [], ""
    if data[:1] == b"\x16":
        scheme = "https"
        try:
            sni = client_hello_names(data)
        except (ValueError, IndexError) as e:
            return ("unreadable ClientHello", str(e))
        if sni != [host] and not (sni == [] and is_ipv4(host)):
            notes.append("SNI: " + (", ".join(sni) or "none"))
        if names is not None and (len(names) != 1 or names[0] not in (None, host)):
            notes.append(f"server_hostname: {names}")
    elif b"\r\n\r\n" in data:
        scheme = "http"
        lines = data.split(b"\r\n\r\n", 1)[0].decode("latin-1").split("\r\n")
        parts = lines[0].split(" ")
        if len(parts) != 3 or not parts[1].startswith("/"):
            notes.append(f"request line: {lines[0]}")
        h = header(lines, "Host")
        if h is None:
            notes.append("no Host header")
        else:
            hh, hport = split_hostport(h)
            if (hh, eff_port(hport, scheme)) != (host, port):
                notes.append(f"Host: {h}")
        if header(lines, "Authorization") is not None:  # credentials taken from the URL
            user = "(Authorization header)"
        if names:
            notes.append(f"server_hostname: {names}")
    else:
        return ("no request head or ClientHello", repr(data[:40]))
    return (scheme, host + "".join(f" ({n})" for n in notes), port, user)


def direct_node(urls, view):
    """tests/compat_direct.js runs Node's http and https clients against its own fixture."""
    if NODE is None:
        return view.skip("node is not installed")
    view.version = "node " + subprocess.run([NODE, "--version"], capture_output=True, text=True).stdout.strip()
    p = subprocess.run([NODE, os.path.join(HERE, "compat_direct.js")],
                       input="".join(json.dumps(u) + "\n" for u in urls).encode(), capture_output=True,
                       timeout=900)
    lines = [json.loads(l) for l in p.stdout.decode().split("\n") if l]
    if p.returncode != 0 or len(lines) != len(urls) + 1:
        raise RuntimeError(f"compat_direct.js failed ({p.returncode}): {p.stderr.decode()[-2000:]}")
    meta = lines.pop()
    view.blocked = meta["violations"] + ([] if meta["guard"] else ["compat_direct.js: the guard did not refuse"])
    return [direct_of([(h, int(port)) for h, port in r["connect"]], [base64.b64decode(b) for b in r["recs"]])
            for r in lines]


class DirectRoute:
    """While active (inside FixtureOnly), the Python clients' direct connections go to the direct
    fixture. Inside each call of `socket.create_connection` (http.client, so urllib.request) or of
    urllib3's `create_connection` (urllib3, requests), the client's one address lookup is answered
    with the fixture's address and recorded as the client's target; any other lookup still meets
    FixtureOnly. `ssl.SSLContext.wrap_socket` records the `server_hostname` it is given."""

    def __init__(self, port):
        self.port, self.armed, self.connects, self.names, self.saved = port, False, [], [], []

    def patch(self, obj, name, value):
        self.saved.append((obj, name, getattr(obj, name)))
        setattr(obj, name, value)

    def __enter__(self):
        lookup = socket.getaddrinfo  # FixtureOnly's guard

        def getaddrinfo(host, port, *args, **kwargs):
            if not self.armed:
                return lookup(host, port, *args, **kwargs)
            self.armed = False
            self.connects.append((host, port))
            return lookup("127.0.0.1", self.port, *args, **kwargs)

        def routed(create):
            def create_connection(*args, **kwargs):
                self.armed = True
                try:
                    return create(*args, **kwargs)
                finally:
                    self.armed = False
            return create_connection

        wrap = ssl.SSLContext.wrap_socket

        def wrap_socket(context, sock, *args, **kwargs):
            self.names.append(kwargs.get("server_hostname", args[3] if len(args) > 3 else None))
            return wrap(context, sock, *args, **kwargs)

        self.patch(socket, "getaddrinfo", getaddrinfo)
        self.patch(socket, "create_connection", routed(socket.create_connection))
        try:
            import urllib3.util.connection as urllib3_connection
            self.patch(urllib3_connection, "create_connection", routed(urllib3_connection.create_connection))
        except ImportError:
            pass
        self.patch(ssl.SSLContext, "wrap_socket", wrap_socket)
        return self

    def __exit__(self, *exc):
        for obj, name, value in reversed(self.saved):
            setattr(obj, name, value)

    def take(self):
        r = (self.connects, self.names)
        self.connects, self.names = [], []
        return r


def one_direct(fixture, route, send):
    if fixture.take() or route.take() != ([], []):
        raise RuntimeError("direct fixture: a connection was not matched to its URL")
    try:
        send()
    except Exception:  # every client fails on the 403 or the TLS alert; that is expected
        pass
    connects, names = route.take()
    return direct_of(connects, [d for _, _, d in fixture.take(len(connects))], names)


def direct_urllib(urls, fixture, route, view):
    import urllib.request
    view.version = "Python " + platform.python_version()
    opener = urllib.request.build_opener(urllib.request.ProxyHandler({}))
    return [one_direct(fixture, route, lambda u=u: opener.open(u, timeout=5)) for u in urls]


# urllib3 and requests load their CA bundle file for every connection (about 9 ms), before the
# handshake. They are given the system's CA directory instead, which is read only when a
# certificate is checked; that never happens here, and the ClientHello does not depend on it.
CA_DIR = ssl.get_default_verify_paths().capath
CA_DIR = CA_DIR if CA_DIR and os.path.isdir(CA_DIR) else None


def direct_urllib3(urls, fixture, route, view):
    try:
        import urllib3
    except ImportError:
        return view.skip("urllib3 is not installed")
    view.version = "urllib3 " + urllib3.__version__
    ca = {"ca_cert_dir": CA_DIR} if CA_DIR else {}
    return [one_direct(fixture, route, lambda u=u: urllib3.PoolManager(retries=False, timeout=5, **ca).request(
        "GET", u, retries=False, redirect=False)) for u in urls]


def direct_requests(urls, fixture, route, view):
    try:
        import requests
    except ImportError:
        return view.skip("requests is not installed")
    view.version = "requests " + requests.__version__

    def send(u):
        with requests.Session() as s:
            s.trust_env, s.verify = False, CA_DIR or True
            s.get(u, timeout=5, allow_redirects=False)
    return [one_direct(fixture, route, lambda u=u: send(u)) for u in urls]


def direct_curl(urls, expected, fixture, view):
    """curl's connection target is tested, not read: with `--connect-to` rules for URLFence's host
    and port, tried in order, the fixture port the connection reaches says whether curl's own host
    and port are those. `%{local_port}` matches each connection to its URL (curl runs one URL at a
    time). `--insecure` only spares curl loading its CA bundle for every transfer (about 9 ms):
    with curl 8.5 its ClientHello has the same extensions with and without it, and the handshake
    never reaches the certificate."""
    curl = shutil.which("curl")
    if curl is None:
        return view.skip("curl is not installed")
    view.version = "curl " + subprocess.run([curl, "--version"], capture_output=True, text=True).stdout.split(" ")[1]
    env = {"PATH": os.environ.get("PATH", "/usr/bin:/bin")}
    a, b, c, d = fixture.ports
    out = [None] * len(urls)
    for start in range(0, len(urls), 500):
        blocks = []
        for i in range(start, min(start + 500, len(urls))):
            _, h, p, _ = expected[i]
            blocks.append("\n".join([
                f"url = {curl_quote(urls[i])}",
                f'connect-to = "{h}:{p}:127.0.0.1:{a}"', f'connect-to = "{h}::127.0.0.1:{b}"',
                f'connect-to = ":{p}:127.0.0.1:{c}"', f'connect-to = "::127.0.0.1:{d}"',
                'output = "/dev/null"', f'write-out = "{i}\\t%{{local_port}}\\t%{{num_connects}}\\n"',
                "globoff", "silent", "max-time = 5", "insecure"]))
        if fixture.take():
            raise RuntimeError("direct fixture: a connection was not matched to its URL")
        proc = subprocess.run([curl, "-q", "-g", "-s", "-K", "-"], input="\nnext\n".join(blocks).encode(),
                              capture_output=True, env=env, timeout=600)
        done = []
        for line in proc.stdout.decode("utf-8", "replace").split("\n"):
            f = line.split("\t")
            if len(f) == 3 and all(x.isdigit() for x in f) and int(f[2]) > 0:
                done.append((int(f[0]), int(f[1]), int(f[2])))
        by_port, unmatched = collections.defaultdict(collections.deque), 0
        for listen, peer, data in fixture.take(sum(n for _, _, n in done)):
            by_port[peer].append((listen, data))
        for i, local, n in done:
            _, h, p, _ = expected[i]
            if n != 1 or not by_port[local]:
                out[i] = ("several connections" if n != 1 else "connection not seen by the fixture", n)
                if by_port[local]:
                    by_port[local].popleft()
                unmatched += n - 1  # curl reports the port of its last connection only
                continue
            listen, data = by_port[local].popleft()
            host = h if listen in (a, b) else f"(not {h})"
            port = p if listen in (a, c) else f"(not {p})"
            out[i] = direct_of([(host, port)], [data])
        if sum(map(len, by_port.values())) != unmatched:
            raise RuntimeError("direct fixture: a connection was not matched to its URL")
    return out


# ---- main ----------------------------------------------------------------------------------------

SELF_TEST = [  # what a naive parser would report; every client reads these differently
    ("http://example.com:pass@evil.com/", ("http", "example.com", 80, "")),
    ("http://evil.com/#@example.com", ("http", "example.com", 80, "")),
    ("https://example.com.evil.com/", ("https", "example.com", 443, "")),
    ("https://example.com:8443/", ("https", "example.com", 443, "")),
    ("http://example.com:8080/", ("http", "example.com", 80, "")),
    ("http://user:pw@example.com/", ("http", "example.com", 80, "")),
    ("http://user@example.com/", ("http", "example.com", 80, "")),
]
# Self-test cases where what a client sends has nothing to show, and what it does instead, which the
# self-test requires exactly (so that a change in the client is noticed).
SELF_TEST_UNSEEN = {
    # On its direct path http.client takes `user:pw@example.com` for host and port, and refuses the
    # "port"; it connects to `user@example.com` as a host, which is reported.
    ("urllib.request", "direct", "http://example.com:pass@evil.com/"): "refused",
    ("urllib.request", "direct", "http://user:pw@example.com/"): "refused",
    # On its direct path urllib3 drops the userinfo: it connects to example.com, sends no credentials.
    ("urllib3", "direct", "http://user:pw@example.com/"): "agree",
    ("urllib3", "direct", "http://user@example.com/"): "agree",
    # requests takes no credentials from a userinfo without a password, and removes the userinfo
    # from the URL it sends to a proxy.
    ("requests", "request", "http://user@example.com/"): "agree",
    ("requests", "direct", "http://user@example.com/"): "agree",
}


def main():
    ap = argparse.ArgumentParser(description="URLFence client compatibility check")
    ap.add_argument("--quick", action="store_true", help="a fixed 1/16 subset of the corpus (what CI runs)")
    ap.add_argument("--require", default="", help="comma-separated clients that must run (a skip then fails)")
    ap.add_argument("--strict", action="store_true", help="also fail when a client refuses an accepted URL")
    ap.add_argument("--json", help="write a JSON report here")
    ap.add_argument("--self-test", action="store_true",
                    help="check that every view reports deliberately wrong expectations, instead of the corpus")
    args = ap.parse_args()
    for k in ("http_proxy", "https_proxy", "all_proxy", "no_proxy", "HTTP_PROXY", "HTTPS_PROXY", "ALL_PROXY",
              "NO_PROXY"):
        os.environ.pop(k, None)
    failed = False

    if args.self_test:
        acc_urls, expected = [u for u, _ in SELF_TEST], [e for _, e in SELF_TEST]
        full, urls = (len(SELF_TEST), digest(acc_urls)), acc_urls
        print(f"self-test: {len(SELF_TEST)} deliberately wrong expectations")
    else:
        urls = corpus()
        full = (len(urls), digest(urls))
        if full != (CORPUS_SIZE, CORPUS_SHA256):
            print(f"corpus changed: {full[0]} URLs, sha256 {full[1]}; update CORPUS_SIZE, CORPUS_SHA256 "
                  "and the README")
            failed = True
        if args.quick:
            urls = urls[::16]
        results = []
        for start in range(0, len(urls), 5000):
            _, out = run_check(urls[start:start + 5000], ["*.com"], schemes=["http", "https"], stdin=True)
            assert len(out) == len(urls[start:start + 5000])
            results += out
        accepted = [(u, r) for u, r in zip(urls, results) if r["decision"] != "reject"]
        acc_urls = [u for u, _ in accepted]
        expected = [expected_of(r) for _, r in accepted]
        print(f"corpus: {full[0]} URLs, sha256 {full[1][:16]}"
              + (f"; quick subset {len(urls)} URLs" if args.quick else "")
              + f"; URLFence accepts {len(acc_urls)} (sha256 {digest(acc_urls)[:16]})")

    views = []
    for name, fn in [("whatwg", parse_whatwg), ("urlsplit", parse_urlsplit),
                     ("urllib.request", parse_urllib_request), ("urllib3", parse_urllib3),
                     ("requests", parse_requests)]:
        v = View(name, "parser")
        v.record_all(acc_urls, expected, fn(acc_urls, v))
        views.append(v)

    fixture, direct = Fixture(), DirectFixture(listeners=4)
    try:
        cp, cr = View("curl", "parser"), View("curl", "request")
        parsed, requested = run_curl(acc_urls, fixture, cp, cr)
        cp.record_all(acc_urls, expected, parsed)
        cr.record_all(acc_urls, expected, requested)
        views.append(cp)
        python_direct = []
        with FixtureOnly([fixture.server.server_address[1]] + direct.ports) as guard:
            for name, fn in [("urllib.request", request_urllib), ("urllib3", request_urllib3),
                             ("requests", request_requests)]:
                v = View(name, "request")
                v.record_all(acc_urls, expected, fn(acc_urls, fixture, v))
                views.append(v)
            with DirectRoute(direct.ports[0]) as route:
                for name, fn in [("urllib.request", direct_urllib), ("urllib3", direct_urllib3),
                                 ("requests", direct_requests)]:
                    v = View(name, "direct")
                    v.record_all(acc_urls, expected, fn(acc_urls, direct, route, v))
                    python_direct.append(v)
        views.append(cr)
        v = View("node", "direct")
        v.record_all(acc_urls, expected, direct_node(acc_urls, v))
        views.append(v)
        views += python_direct
        v = View("curl", "direct")
        v.record_all(acc_urls, expected, direct_curl(acc_urls, expected, direct, v))
        views.append(v)
    finally:
        fixture.close()
        direct.close()
    views.append(View("node", "request").skip("this harness has no proxy view for Node's http module",
                                              status="not covered"))
    blocked = guard.blocked + [b for v in views for b in v.blocked]
    if blocked:
        print(f"  a client tried to reach {len(blocked)} addresses other than the fixture, e.g. {blocked[:3]}")
        failed = True

    print(f"{'client':<15} {'view':<8} {'version':<34} {'agree':>7} {'refused':>8} {'differs':>8}  status")
    for v in views:
        if v.ran:
            print(f"{v.client:<15} {v.kind:<8} {v.version:<34} {v.agree:>7} {len(v.refused):>8} "
                  f"{len(v.differs):>8}  ran")
        else:
            print(f"{v.client:<15} {v.kind:<8} {v.version:<34} {'-':>7} {'-':>8} {'-':>8}  {v.status}")
    unseen = 0
    for v in views:
        if not v.ran:
            continue
        if args.self_test:
            for u in acc_urls:
                want = SELF_TEST_UNSEEN.get((v.client, v.kind, u), "differs")
                unseen += want != "differs"
                if v.outcome[u] != want:
                    print(f"  {v.client} {v.kind} {v.outcome[u]} on {json.dumps(u)}, expected {want}")
                    failed = True
            continue
        for u in v.refused[:10]:
            print(f"  {v.client} {v.kind} refused: {json.dumps(u)}")
        for u, g in v.differs[:10]:
            print(f"  {v.client} {v.kind} differs: {json.dumps(u)} -> {g}")
        if len(v.refused) > len(acc_urls) // 100:
            print(f"  {v.client} {v.kind} refused {len(v.refused)} of {len(acc_urls)}: the view is broken")
            failed = True
        failed |= bool(v.differs) or (args.strict and bool(v.refused))
    required = {c for c in args.require.split(",") if c}
    for c in sorted(required - {v.client for v in views}):
        print(f"  unknown client in --require: {c}")
        failed = True
    for v in views:
        if v.client in required and not v.ran and not v.status.startswith("not covered"):
            print(f"  required client did not run: {v.client} {v.kind} ({v.status})")
            failed = True
    ran = [v for v in views if v.ran]
    skipped = [v for v in views if v.status.startswith("SKIPPED")]
    if args.json:
        with open(args.json, "w") as f:
            json.dump({"result": "FAILED" if failed else "OK", "self_test": args.self_test, "strict": args.strict,
                       "require": sorted(required),
                       "corpus": {"urls": full[0], "sha256": full[1], "quick": args.quick, "checked": len(urls),
                                  "accepted": len(acc_urls), "accepted_sha256": digest(acc_urls)},
                       "views": [{"client": v.client, "view": v.kind, "version": v.version, "status": v.status,
                                  "agree": v.agree, "refused": v.refused,
                                  "differs": [[u, list(map(str, g))] for u, g in v.differs]} for v in views]},
                      f, indent=1)
    if args.self_test:
        print(f"self-test: {'FAILED' if failed else 'OK'} ({len(ran)} views ran; each must report all "
              f"{len(acc_urls)} differences, except {unseen} listed cases where the client sends nothing "
              f"that shows one; {len(skipped)} skipped)")
    else:
        print(f"compat: {'FAILED' if failed else 'OK'} ({len(ran)} views ran on {len(acc_urls)} accepted URLs; "
              f"{sum(len(v.differs) for v in ran)} disagreements, {sum(len(v.refused) for v in ran)} refusals; "
              f"{len(skipped)} skipped, which count as nothing)")
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
