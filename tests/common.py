"""Shared helpers: run the `urlfence` binary, ask a WHATWG URL parser (Node's `URL`), and a Python
model of the documented matching rules."""
import json
import os
import shutil
import subprocess

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
BIN = os.environ.get("URLFENCE_BIN", os.path.join(ROOT, ".lake", "build", "bin", "urlfence"))
NODE = shutil.which("node")


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
