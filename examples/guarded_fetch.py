"""Fetch a URL for an agent: URLFence decides, then exactly the checked URL is requested.

    status, body, hops = guarded_fetch("https://docs.python.org/3/", allow=["docs.python.org"])

An example to adapt, not a hardened HTTP client:

1. `urlfence check` decides. Its answer is used only if it is one JSON object for exactly this
   URL, and the exit status agrees with the decision; a timeout, a missing binary, malformed
   output or input it cannot take (a NUL, say) refuses.
2. A GET goes to exactly the string that was checked, never to a URL rebuilt from another
   parser's reading of it.
3. Redirects are never followed by urllib: each `Location` is resolved against the current URL
   and checked again before the next request, at most `max_redirects` times.

The last response is returned whatever its status (a 404, a 304, a 3xx without `Location`), with
the body cut at `max_bytes`. `proxies` is passed to urllib's `ProxyHandler`; left as None, urllib
uses the `*_proxy` and `no_proxy` environment variables. `TIMEOUT` applies to each socket
operation, not to the whole fetch.

This is the URL string only. An allowed name can still resolve to an internal address, a proxy or
server may parse the URL again, and the port and path are not restricted: pair it with egress
controls. See the README's "What it does not cover".
"""
import http.client
import json
import os
import subprocess
import urllib.error
import urllib.parse
import urllib.request

URLFENCE = os.environ.get("URLFENCE_BIN", "urlfence")
TIMEOUT = 10


class Refused(Exception):
    """URLFence did not allow a URL on the way (`hops` lists every check), or a request failed."""

    def __init__(self, message, hops):
        super().__init__(message)
        self.hops = hops


def check(url, allow, deny=(), schemes=("https",)):
    """URLFence's answer for one URL, as a dict; a `reject` whenever the answer is unusable."""
    for name, value in (("allow", allow), ("deny", deny), ("schemes", schemes)):
        if isinstance(value, (str, bytes)):
            raise TypeError(f"{name} must be a list of strings, not a single string")
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


class NoRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, *args, **kwargs):
        return None  # hand the 3xx back to guarded_fetch, which checks Location first


def guarded_fetch(url, allow, deny=(), schemes=("https",), max_redirects=3, proxies=None, max_bytes=1 << 20):
    """`(status, body, hops)` for the last response, or `Refused`."""
    opener = urllib.request.build_opener(urllib.request.ProxyHandler(proxies), NoRedirect())
    hops = []
    for _ in range(max_redirects + 1):
        r = check(url, allow, deny, schemes)
        hops.append({"url": url, "decision": r["decision"], "reason": r.get("reason")})
        if r["decision"] != "allow":
            why = f" ({r['reason']})" if r.get("reason") else ""
            raise Refused(f"{r['decision']}{why}: {url!r}", hops)
        try:
            try:
                resp = opener.open(url, timeout=TIMEOUT)  # exactly the string URLFence checked
            except urllib.error.HTTPError as e:
                resp = e  # an error status still has headers and a body
            with resp:
                status, headers, body = resp.status, resp.headers, resp.read(max_bytes)
        except (OSError, http.client.HTTPException, ValueError) as e:  # URLError is an OSError
            raise Refused(f"request failed: {getattr(e, 'reason', e)}", hops) from e
        if status in (301, 302, 303, 307, 308) and headers.get("Location"):
            url = urllib.parse.urljoin(url, headers["Location"])
            continue
        return status, body, hops
    raise Refused(f"more than {max_redirects} redirects", hops)
