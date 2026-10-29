"""Shared helpers: run the `urlfence` binary, ask a WHATWG URL parser (Node's `URL`), and a Python
model of the documented matching rules. Importing it also keeps the process on loopback (below)."""
import ipaddress
import json
import os
import shutil
import socket
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
BIN = os.environ.get("URLFENCE_BIN", os.path.join(ROOT, ".lake", "build", "bin", "urlfence"))
NODE = shutil.which("node")


# ---- nothing leaves the machine -------------------------------------------------------------------
# Every test module imports this one (directly or through compat), so in a process that runs tests,
# from the first import on:
# * `socket.socket.connect` and `connect_ex` refuse any address but a numeric one in 127.0.0.0/8 or
#   ::1, before the C library could look up a name, and close the socket. Every socket made with the
#   `socket` module goes through them: those of http.client, urllib and ssl (`SSLSocket.connect`)
#   too.
# * An audit hook, which cannot be removed, refuses the same for the `socket.connect`,
#   `socket.sendto` and `socket.sendmsg` events, whatever made the socket, and refuses to look up a
#   name (`socket.getaddrinfo`, `gethostbyname`, `gethostbyname_ex`; an IP literal is not looked up)
#   or an address (`gethostbyaddr`, `getnameinfo`, but for loopback). These events come before the
#   call, so a test that forgets to replace `getaddrinfo` asks no resolver. (For a connect, sendto
#   or sendmsg, the event comes after the address is parsed: a name given straight to
#   `_socket.socket.connect`, past the wrapper above, or to `sendto` or `sendmsg`, which no wrapper
#   covers, would be looked up first, and only the connection or the send refused.)
# A refusal raises Outbound, a RuntimeError and not an OSError, so that code that tries the next
# address or reports a failed connection does not take it for one; OUTBOUND lists each refusal.
# Subprocesses (node, openssl, curl, the binary) are not covered: the Node driver has its own guard.

class Outbound(RuntimeError):
    """A test tried to reach beyond loopback (or to look up a name), and tests/common.py refused."""


OUTBOUND = []  # (what, target) for each refusal
_LOOPBACK4 = ipaddress.ip_network("127.0.0.0/8")
_LOOPBACK6 = ipaddress.ip_address("::1")


def _numeric(host):
    """`host` as an IPv4 or IPv6 address, or None for anything else (a name, say)."""
    if isinstance(host, bytes):
        host = host.decode("ascii", "replace")
    try:
        return ipaddress.ip_address(host)
    except ValueError:
        return None


def _loopback(address):
    """Whether a socket address is a numeric one in 127.0.0.0/8 or ::1 (an AF_UNIX path is not)."""
    if not isinstance(address, tuple) or not address or not isinstance(address[0], (str, bytes)):
        return False
    ip = _numeric(address[0])
    return ip is not None and (ip == _LOOPBACK6 or (ip.version == 4 and ip in _LOOPBACK4))


def _refuse(what, target):
    OUTBOUND.append((what, target))
    raise Outbound(f"tests/common.py: refusing {what} {target!r}: tests stay on loopback")


def _confined(real):
    def connect(self, address):
        if not _loopback(address):
            self.close()
            _refuse(real.__name__, address)
        return real(self, address)
    connect.__name__ = connect.__qualname__ = real.__name__
    return connect


def _audit(event, args):
    if not event.startswith("socket."):
        return
    if event in ("socket.connect", "socket.sendto", "socket.sendmsg"):
        if (event == "socket.connect" or args[1] is not None) and not _loopback(args[1]):
            _refuse(event, args[1])
    elif event in ("socket.getaddrinfo", "socket.gethostbyname", "socket.gethostbyname_ex"):
        if args[0] is not None and _numeric(args[0]) is None:
            _refuse(event, args[0])
    elif event == "socket.gethostbyaddr":
        if not _loopback((args[0],)):
            _refuse(event, args[0])
    elif event == "socket.getnameinfo":
        if not _loopback(args[0]):
            _refuse(event, args[0])


if not getattr(socket.socket.connect, "confined", False):
    socket.socket.connect = _confined(socket.socket.connect)
    socket.socket.connect_ex = _confined(socket.socket.connect_ex)
    socket.socket.connect.confined = True
    sys.addaudithook(_audit)


def run_raw(args, data=None):
    """Run `urlfence` with `args` and stdin bytes `data`; return (exit status, decoded results)."""
    proc = subprocess.run([BIN] + list(args), input=data, capture_output=True, check=False)
    out = proc.stdout.decode("ascii")  # the output is ASCII by design
    return proc.returncode, [json.loads(l) for l in out.split("\n") if l]


def run_check(urls, allow, deny=(), schemes=None, stdin=False):
    args = ["check"]
    for a in allow:
        args += ["--allow", a]
    for d in deny:
        args += ["--deny", d]
    for s in schemes or []:
        args += ["--scheme", s]
    if stdin:
        return run_raw(args + ["--stdin"], "".join(u + "\n" for u in urls).encode())
    return run_raw(args + ["--"] + list(urls))


def whatwg(urls):
    """What the WHATWG URL parser makes of each URL (None when Node is not installed)."""
    if NODE is None:
        return None
    data = "".join(json.dumps(u) + "\n" for u in urls).encode()
    proc = subprocess.run([NODE, os.path.join(ROOT, "tests", "whatwg.js")], input=data,
                          capture_output=True, check=True)
    return [json.loads(l) for l in proc.stdout.decode().split("\n") if l]


# ---- the matching rules, on a hostname -----------------------------------------------------------

def pattern_matches(pattern, host):
    """`*.d` matches strict subdomains of d (label by label); anything else matches exactly."""
    if pattern.startswith("*."):
        d = pattern[2:]
        return host.endswith("." + d) and not is_ipv4(host)
    return host == pattern


def is_ipv4(host):
    parts = host.split(".")
    return len(parts) == 4 and all(p.isdigit() for p in parts)


def model_decision(host, scheme, allow, deny=(), schemes=("https",)):
    ok = scheme in schemes and any(pattern_matches(p, host) for p in allow) and \
        not any(pattern_matches(p, host) for p in deny)
    return "allow" if ok else "deny"
