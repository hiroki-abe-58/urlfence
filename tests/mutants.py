"""Mutation check: do the proofs and the tests notice plausible bugs?

Copies the repository to a temporary directory and, for each mutant, edits the source, rebuilds and
runs the test suite. A mutant counts as caught when the build fails (a proof or a build-time
example no longer holds; the file is reported) or the suite fails. The unmutated control must build
and pass. Exits 1 otherwise.

    python3 tests/mutants.py
"""
import os
import shutil
import subprocess
import sys
import tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

MATCH = "  | .sub d, .domain ls => !d.isEmpty && decide (d.length < ls.length) && d.isSuffixOf ls\n"
NODE_EXAMPLE = "examples/guarded_fetch.mjs"
CHECK = "    if pol.schemes.contains u.scheme && pol.allow.any (·.matches u.host) && !pol.deny.any (·.matches u.host)\n"

# name -> list of (file, old text, new text)
MUTANTS = {
    "M0 control (unmutated)": [],
    # Bugs from the advisories in the README.
    "M1 suffix without the dot (CVE-2026-33393 style)": [
        ("UrlFence/Policy.lean", MATCH, "  | .sub d, .domain ls => (join '.' d).isSuffixOf (join '.' ls)\n")],
    "M2 exact match by string prefix (CVE-2026-24052 style)": [
        ("UrlFence/Policy.lean", "  | .exact h', h => decide (h' = h)\n", "  | .exact h', h => h'.render.isPrefixOf h.render\n")],
    "M3 userinfo not checked": [
        ("UrlFence/Url.lean", "    if '@' ∈ auth then .error .userinfo\n    else if", "    if")],
    "M4 percent signs allowed in the authority": [
        ("UrlFence/Url.lean", "    else if '%' ∈ auth then .error .percent\n", "")],
    "M5 backslash allowed": [
        ("UrlFence/Url.lean", "def okChar (c : Char) : Bool := '!' ≤ c && c ≤ '~' && c ≠ '\\\\'",
         "def okChar (c : Char) : Bool := '!' ≤ c && c ≤ '~'")],
    # Other plausible slips.
    "M6 subdomain pattern also matches the domain itself": [
        ("UrlFence/Policy.lean", MATCH, "  | .sub d, .domain ls => !d.isEmpty && decide (d.length ≤ ls.length) && d.isSuffixOf ls\n")],
    "M7 deny patterns ignored": [
        ("UrlFence/Policy.lean", CHECK, "    if pol.schemes.contains u.scheme && pol.allow.any (·.matches u.host)\n")],
    "M8 scheme not checked": [
        ("UrlFence/Policy.lean", CHECK, "    if pol.allow.any (·.matches u.host) && !pol.deny.any (·.matches u.host)\n")],
    "M9 number-like last label accepted as a domain": [
        ("UrlFence/Host.lean", "    | some l => !numberLike l\n", "    | some _ => true\n")],
    "M10 octets with leading zeros (octal to WHATWG)": [
        ("UrlFence/Host.lean", "  0 < l.length && l.length ≤ 3 && l.all isDigit && (l.length = 1 || l.head? != some '0') &&\n",
         "  0 < l.length && l.length ≤ 3 && l.all isDigit &&\n")],
    "M11 ports with leading zeros": [
        ("UrlFence/Url.lean", "  0 < p.length && p.length ≤ 5 && p.all isDigit && (p.length = 1 || p.head? != some '0') &&\n",
         "  0 < p.length && p.length ≤ 5 && p.all isDigit &&\n")],
    "M13 `;` also ends the authority (the boundary a reviewer probed)": [
        ("UrlFence/Url.lean", "def isDelim (c : Char) : Bool := c = '/' || c = '?' || c = '#'",
         "def isDelim (c : Char) : Bool := c = '/' || c = '?' || c = '#' || c = ';'")],
    "M14 IDNA A-labels (xn--) accepted": [
        ("UrlFence/Host.lean", " &&\n    l.take 4 != ['x', 'n', '-', '-']", "")],
    "M15 port 0 accepted": [
        ("UrlFence/Url.lean", "    decValue p ≤ 65535 && p != ['0']", "    decValue p ≤ 65535")],
    "M12 uppercase letters accepted in hosts": [
        ("UrlFence/Host.lean", "def isLower (c : Char) : Bool := 'a' ≤ c && c ≤ 'z'",
         "def isLower (c : Char) : Bool := ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z')")],
    # The address check (UrlFence/Addr), in the style of the advisories in Addr/Examples.lean.
    "A1 IPv4-mapped addresses not decoded (CVE-2026-49857 style)": [
        ("UrlFence/Addr/Check.lean", "  mapped96.contains a || cfg.nat64.any fun p =>", "  cfg.nat64.any fun p =>")],
    "A2 embedded IPv4 address taken at the wrong offset": [
        ("UrlFence/Addr/Check.lean", "def low32 (a : BitVec 128) : BitVec 32 := a.setWidth 32",
         "def low32 (a : BitVec 128) : BitVec 32 := (a >>> 16).setWidth 32")],
    "A3 6to4 row (2002::/16) dropped from the registry": [
        ("UrlFence/Addr/Registry.lean", '  ⟨⟨ip6 [0x2002, 0, 0, 0, 0, 0, 0, 0], 16⟩, "6to4", .na⟩,\n', "")],
    "A4 prefix length off by one": [
        ("UrlFence/Addr/Bits.lean", "  a >>> (w - p.len) == p.base >>> (w - p.len)",
         "  a >>> (w - p.len + 1) == p.base >>> (w - p.len + 1)")],
    "A5 ISATAP 0200:5efe form not decoded": [
        ("UrlFence/Addr/Check.lean", "&&& 0xfcffffff#32) == 0x00005efe#32", "&&& 0xfdffffff#32) == 0x00005efe#32")],
    "A6 IPv4 multicast allowed": [
        ("UrlFence/Addr/Check.lean", "  !unreachable4 v && !multicast4.contains v && !cfg.deny4.any",
         "  !unreachable4 v && !cfg.deny4.any")],
    "A7 64:ff9b::/96 allowed as global without decoding": [
        ("UrlFence/Addr/Check.lean", "     else global6.contains a && !unreachable6 a &&",
         "     else (global6.contains a || wellKnown96.contains a) && !unreachable6 a &&")],
    "A8 the CLI ignores a NAT64 prefix that nat64Ok rejects": [
        ("Main.lean", "      if !Addr.nat64Ok p.base then", "      if false then")],
    # The Node example (examples/guarded_fetch.mjs), for tests/test_guarded_fetch_node.py.
    "N1 Node example: a denied address refuses only on the first hop": [
        (NODE_EXAMPLE, '    if (a.decision !== "allow") {', '    if (a.decision !== "allow" && hops.length === 1) {')],
    "N2 Node example: connects to the URL's host name, not the checked address": [
        (NODE_EXAMPLE, "  if (addrKey(addr) === null) throw new TypeError(`not a numeric address: ${JSON.stringify(addr)}`);\n",
         ""),
        (NODE_EXAMPLE, "  const where = { host: addr, port, lookup: noLookup, timeout };",
         "  const where = { host: addr, port, timeout };"),
        (NODE_EXAMPLE, "      sock = await openSocket(a.addr, port, {", "      sock = await openSocket(host, port, {")],
    "N3 Node example: an answer's addr not compared with the address checked": [
        (NODE_EXAMPLE, "    if (addrKey(a.addr) === null || addrKey(a.addr) !== addrKey(a.input)) {",
         "    if (addrKey(a.addr) === null) {")],
}


def main():
    tmp = tempfile.mkdtemp()
    repo = os.path.join(tmp, "urlfence")
    shutil.copytree(ROOT, repo, symlinks=True)
    originals = {}
    ok = True
    try:
        for name, edits in MUTANTS.items():
            for f, text in originals.items():
                open(os.path.join(repo, f), "w", encoding="utf-8").write(text)
            for f, old, new in edits:
                p = os.path.join(repo, f)
                src = originals.setdefault(f, open(p, encoding="utf-8").read())
                assert src.count(old) == 1, f"{name}: hook not found once in {f}: {old!r}"
                open(p, "w", encoding="utf-8").write(src.replace(old, new))
            b = subprocess.run(["lake", "build"], cwd=repo, capture_output=True, text=True)
            control = name.startswith("M0")
            if b.returncode != 0:
                log = b.stdout + b.stderr
                files = sorted({l.split("error: ", 1)[1].split(":", 1)[0] for l in log.splitlines()
                                if "error: UrlFence/" in l or "error: Main.lean" in l})
                if files and all(f.endswith("/Examples.lean") for f in files):
                    layer = "build-time examples"
                elif files and all(f.startswith("UrlFence/") for f in files):
                    layer = "proofs"
                else:
                    layer = "build"
                caught = f"build failed in {', '.join(files) or '?'} ({layer})"
                good = not control
            else:
                t = subprocess.run([sys.executable, "-m", "unittest", "discover", "-s", "tests"], cwd=repo,
                                   capture_output=True, text=True)
                caught = "suite passed" if t.returncode == 0 else "suite failed"
                good = (t.returncode == 0) == control
            ok &= good
            print(f"{name}: {caught} -> {'ok' if good else 'UNEXPECTED'}", flush=True)
    finally:
        shutil.rmtree(tmp)
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
