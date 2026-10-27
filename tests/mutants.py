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
                                if "error: UrlFence/" in l})
                layer = "build-time examples" if files == ["UrlFence/Examples.lean"] else "proofs"
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
