"""Fetch a URL for an agent: URLFence decides on the URL and on every address its host resolves to,
and only a checked address is connected to.

    status, body, hops = guarded_fetch("https://docs.python.org/3/", allow=["docs.python.org"])

An example to adapt, not a hardened HTTP client:

1. `urlfence check` decides on the URL. Its answer is used only if it is one JSON object for exactly
   this URL, and the exit status agrees with the decision; a timeout, a missing binary, malformed
   output or input it cannot take (a NUL, say) refuses.
2. Pinned (`pin=True`, the default): the host is resolved once with `getaddrinfo`, and `urlfence
   addr` checks every address it resolves to (with `deny_addr` and `nat64` as its `--deny` and
   `--nat64`). If any address is denied, or the answer is unusable in the same ways as above, the
   fetch is refused before any connection is opened. Otherwise the request goes over a TCP
   connection that guarded_fetch opens itself to a checked address (`open_socket`), so the name is
   not resolved again between the check and the connection; the `Host` header, the TLS server name
   and the certificate check use the URL's host. A proxy resolves the name itself, so nothing
   could be pinned: with `pin=True`, passing `proxies` is an error, and a proxy set in the
   environment for the URL's scheme refuses (`no_proxy` is honoured).
   With `pin=False`, urllib requests the URL as before: urllib or a proxy resolves the name again,
   and no address is checked; a proxy must then enforce its own address policy.
3. The request (GET) is for exactly the URL that was checked: unpinned, urllib gets that string;
   pinned, the request target is the checked URL after its host and port, without the fragment.
4. Redirects are never followed by the HTTP library: each `Location` is resolved against the
   current URL and checked again, the URL and (pinned) the addresses, before the next request, at
   most `max_redirects` times. A name that answered a public address on one hop and a private one on
   the next is refused at the second.

Pinning is the default because it closes the gap a URL check leaves open, an allowed name that
resolves to an internal address (also after a redirect or a rebinding), at the cost of not working
through a proxy.

The last response is returned whatever its status (a 404, a 304, a 3xx without `Location`), with
the body cut at `max_bytes`; a body that ends before its Content-Length, because the connection
closed early (over TLS also without close_notify), refuses. `TIMEOUT` applies to each socket
operation, not to the whole fetch.
`hops` lists each check: the URL's decision and, pinned, each address's.

What is still not covered: the port and path are not restricted, a server on an allowed address may
forward the request, and only TCP is pinned. See the README's "What it does not cover".
"""
import http.client
import ipaddress
import json
import os
import socket
import ssl
import subprocess
import urllib.error
import urllib.parse
import urllib.request

URLFENCE = os.environ.get("URLFENCE_BIN", "urlfence")
TIMEOUT = 10


class Refused(Exception):
    """URLFence did not allow a URL or an address on the way (`hops` lists every check), or a
    request failed."""

    def __init__(self, message, hops):
        super().__init__(message)
        self.hops = hops


def _strings(**lists):
    for name, value in lists.items():
        if isinstance(value, (str, bytes)):
            raise TypeError(f"{name} must be a list of strings, not a single string")


def check(url, allow, deny=(), schemes=("https",)):
    """URLFence's answer for one URL, as a dict; a `reject` whenever the answer is unusable."""
    _strings(allow=allow, deny=deny, schemes=schemes)
    args = [URLFENCE, "check"]
    for a in allow:
        args += ["--allow", a]
    for d in deny:
        args += ["--deny", d]
    for s in schemes:
        args += ["--scheme", s]
    try:
        p = subprocess.run(args + ["--", url], stdin=subprocess.DEVNULL, capture_output=True, timeout=TIMEOUT,
                           check=False)
    except (OSError, ValueError, TypeError, subprocess.SubprocessError) as e:
        return {"decision": "reject", "reason": f"urlfence did not run: {e}"}
    if p.returncode == 2:  # a usage error, e.g. an invalid pattern
        return {"decision": "reject", "reason": "urlfence: " + p.stderr.decode("utf-8", "replace").strip()}
    lines = p.stdout.decode("ascii", "replace").split("\n")
    if len(lines) != 2 or lines[1] != "":
        return {"decision": "reject", "reason": f"unexpected urlfence output (exit {p.returncode})"}
    try:
        r = json.loads(lines[0])
    except ValueError:
        r = None
    if not isinstance(r, dict) or r.get("input") != url:
        return {"decision": "reject", "reason": "urlfence answered for something else"}
    if r.get("decision") not in ("allow", "deny", "reject"):
        return {"decision": "reject", "reason": "urlfence gave no decision"}
    # The exit status is 0 exactly when every URL is allowed; a mismatch means a confused answer.
    if (r["decision"] == "allow") != (p.returncode == 0):
        return {"decision": "reject", "reason": f"urlfence exit {p.returncode} disagrees with its decision"}
    return r


def check_addrs(addrs, deny=(), nat64=()):
    """URLFence's answers for these address strings, as `(answers, None)`, or `(None, reason)` when
    there is no usable answer."""
    _strings(deny=deny, nat64=nat64)
    args = [URLFENCE, "addr"]
    for d in deny:
        args += ["--deny", d]
    for n in nat64:
        args += ["--nat64", n]
    try:
        p = subprocess.run(args + ["--", *addrs], stdin=subprocess.DEVNULL, capture_output=True,
                           timeout=TIMEOUT, check=False)
    except (OSError, ValueError, TypeError, subprocess.SubprocessError) as e:
        return None, f"urlfence did not run: {e}"
    if p.returncode == 2:  # a usage error, e.g. an invalid prefix, or no address
        return None, "urlfence: " + p.stderr.decode("utf-8", "replace").strip()
    lines = p.stdout.decode("ascii", "replace").split("\n")
    if len(lines) != len(addrs) + 1 or lines[-1] != "":
        return None, f"unexpected urlfence output (exit {p.returncode})"
    answers = []
    for a, line in zip(addrs, lines):
        try:
            r = json.loads(line)
        except ValueError:
            r = None
        if not isinstance(r, dict) or r.get("input") != a or r.get("decision") not in ("allow", "deny", "reject"):
            return None, "urlfence answered for something else"
        answers.append(r)
    if all(r["decision"] == "allow" for r in answers) != (p.returncode == 0):
        return None, f"urlfence exit {p.returncode} disagrees with its decisions"
    return answers, None


def resolve(host, port):
    """The distinct addresses `getaddrinfo` gives for a TCP connection to host:port, in its order.
    A scoped IPv6 address keeps its scope (`%n`), which URLFence refuses."""
    out = []
    for family, _, _, _, sockaddr in socket.getaddrinfo(host, port, type=socket.SOCK_STREAM):
        if family == socket.AF_INET6:
            a = sockaddr[0] if not sockaddr[3] or "%" in sockaddr[0] else f"{sockaddr[0]}%{sockaddr[3]}"
        elif family == socket.AF_INET:
            a = sockaddr[0]
        else:
            continue
        if a not in out:
            out.append(a)
    return out


def open_socket(addr, port):
    """A TCP connection to exactly this numeric address and port. Anything that is not an IPv4 or
    IPv6 address in numeric form (a name, a scoped address) is a ValueError, so nothing is resolved
    here. (Most tests replace this function to send the connection to a local fixture.)"""
    family = socket.AF_INET6 if ":" in addr else socket.AF_INET
    try:
        socket.inet_pton(family, addr)
    except (OSError, TypeError) as e:
        raise ValueError(f"not a numeric address: {addr!r}") from e
    s = socket.socket(family, socket.SOCK_STREAM)
    try:
        s.settimeout(TIMEOUT)
        s.connect((addr, port))
    except BaseException:
        s.close()
        raise
    return s


def read_body(resp, max_bytes):
    """At most `max_bytes` of the body of `resp`. http.client's `read(amt)` returns a body cut short
    of its Content-Length as if it were whole (an early close, or over TLS an EOF without
    close_notify, reads as its end); here that is an IncompleteRead, so the request failed."""
    body = resp.read(max_bytes)
    left = getattr(resp, "length", None)  # what Content-Length still promises (None without one)
    if len(body) < max_bytes and left:
        raise http.client.IncompleteRead(body, left)
    return body


class PinnedHTTPConnection(http.client.HTTPConnection):
    """http.client's connection for `host`, over a socket to the checked address `addr`."""

    def __init__(self, host, port, addr):
        super().__init__(host, port, timeout=TIMEOUT)
        self.addr = addr

    def connect(self):
        self.sock = open_socket(self.addr, self.port)


class PinnedHTTPSConnection(PinnedHTTPConnection):
    """The same over TLS, with `host` as the server name and the name the certificate must match."""
    default_port = 443

    def __init__(self, host, port, addr, context):
        super().__init__(host, port, addr)
        self.context = context

    def connect(self):
        super().connect()
        self.sock = self.context.wrap_socket(self.sock, server_hostname=self.host)


def pinned_get(url, r, hop, hops, deny_addr, nat64, context, max_bytes):
    """GET `url`, which URLFence read as `r`, over a connection to a checked address of its host."""
    scheme, host, port = r.get("scheme"), r.get("host"), r.get("port")
    prefix = f"{scheme}://{host}" + ("" if port is None else f":{port}")
    if scheme not in ("http", "https") or not isinstance(host, str) or not url.startswith(prefix):
        raise Refused("urlfence's reading of the URL does not match it", hops)
    target = url[len(prefix):].split("#", 1)[0]  # path and query, as checked; empty or `?...`
    if not target.startswith("/"):
        target = "/" + target
    port_n = int(port) if port is not None else (443 if scheme == "https" else 80)
    env = urllib.request.getproxies()
    if (env.get(scheme) or env.get("all")) and not urllib.request.proxy_bypass(host):
        raise Refused(f"a proxy is set in the environment for {scheme}; pinning needs a direct "
                      "connection (use pin=False to go through the proxy)", hops)
    try:
        addrs = resolve(host, port_n)
    except (OSError, UnicodeError) as e:
        raise Refused(f"could not resolve {host!r}: {e}", hops) from e
    if not addrs:
        raise Refused(f"{host!r} has no address", hops)
    answers, why = check_addrs(addrs, deny_addr, nat64)
    if answers is None:
        hop["addrs"] = [{"addr": a, "decision": "reject", "reason": why} for a in addrs]
        raise Refused(f"reject ({why}): the addresses of {host!r}", hops)
    hop["addrs"] = [{"addr": a["input"], "decision": a["decision"], "reason": a.get("reason")} for a in answers]
    for a in answers:
        if a["decision"] != "allow":
            raise Refused(f"{a['decision']} ({a.get('reason')}): {host!r} resolves to {a['input']}", hops)
        # Connect only to the address that was checked: the printed form must be that address.
        try:
            same = ipaddress.ip_address(a.get("addr")) == ipaddress.ip_address(a["input"])
        except (TypeError, ValueError):
            same = False
        if not same:
            raise Refused(f"urlfence printed {a.get('addr')!r} for {a['input']!r}", hops)
    failure = None
    for a in answers:  # every one is allowed; connect to the first that answers
        if scheme == "https":
            conn = PinnedHTTPSConnection(host, port_n, a["addr"], context or ssl.create_default_context())
        else:
            conn = PinnedHTTPConnection(host, port_n, a["addr"])
        try:
            try:
                conn.connect()
            except OSError as e:
                failure = e
                continue
            hop["connected"] = a["addr"]
            conn.request("GET", target, headers={"Connection": "close"})
            with conn.getresponse() as resp:  # closed on every path, as unpinned
                return resp.status, resp.headers, read_body(resp, max_bytes)
        except (OSError, http.client.HTTPException, ValueError) as e:
            raise Refused(f"request failed: {e}", hops) from e
        finally:
            conn.close()
    raise Refused(f"request failed: {failure}", hops)


class NoRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, *args, **kwargs):
        return None  # hand the 3xx back to guarded_fetch, which checks Location first


def guarded_fetch(url, allow, deny=(), schemes=("https",), max_redirects=3, proxies=None, max_bytes=1 << 20,
                  pin=True, deny_addr=(), nat64=(), context=None):
    """`(status, body, hops)` for the last response, or `Refused`. `deny_addr` and `nat64` are
    prefixes for `urlfence addr --deny` and `--nat64`; `context` is the `ssl.SSLContext` for
    pinned https (a default context if None)."""
    if pin and proxies is not None:
        raise ValueError("a proxy resolves the name itself, so nothing can be pinned: pass pin=False to use one")
    _strings(deny_addr=deny_addr, nat64=nat64)
    opener = None if pin else urllib.request.build_opener(urllib.request.ProxyHandler(proxies), NoRedirect())
    hops = []
    for _ in range(max_redirects + 1):
        r = check(url, allow, deny, schemes)
        hop = {"url": url, "decision": r["decision"], "reason": r.get("reason")}
        hops.append(hop)
        if r["decision"] != "allow":
            why = f" ({r['reason']})" if r.get("reason") else ""
            raise Refused(f"{r['decision']}{why}: {url!r}", hops)
        if pin:
            status, headers, body = pinned_get(url, r, hop, hops, deny_addr, nat64, context, max_bytes)
        else:
            try:
                try:
                    resp = opener.open(url, timeout=TIMEOUT)  # exactly the string URLFence checked
                except urllib.error.HTTPError as e:
                    resp = e  # an error status still has headers and a body
                with resp:
                    status, headers, body = resp.status, resp.headers, read_body(resp, max_bytes)
            except (OSError, http.client.HTTPException, ValueError) as e:  # URLError is an OSError
                raise Refused(f"request failed: {getattr(e, 'reason', e)}", hops) from e
        if status in (301, 302, 303, 307, 308) and headers.get("Location"):
            url = urllib.parse.urljoin(url, headers["Location"])
            continue
        return status, body, hops
    raise Refused(f"more than {max_redirects} redirects", hops)
