"""Compare the registry tables of UrlFence/Addr/Registry.lean with the IANA CSV files in data/.

    python3 scripts/check_registry.py

For every CSV row (one per block for a row that lists two), in order: the block (parsed with
Python's ipaddress, so the comparison does not depend on URLFence's own parser), its length, the
"Globally Reachable" value without its footnote mark, and the name must equal those of the Lean row
at the same position, and the Lean table must have no other rows. The block as printed by URLFence
must also be the text of the CSV file. The files' SHA-256 must be those in data/README.md. Needs
lake (the Lean tables are printed by scripts/Registry.lean). Exits 1 on any difference.
"""
import csv
import hashlib
import ipaddress
import os
import re
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
FILES = {
    "ROW4": ("data/iana-ipv4-special-registry.csv", 4,
             "cbc4b7653c8bc640ba1e8e5d4ebbf11e7c7a1d867e7f1593aad001d3f8632aac"),
    "ROW6": ("data/iana-ipv6-special-registry.csv", 6,
             "bf56772aef97fbf9b4a27c98b8511f2bb1ba96da4b9ccc12ab203a2496faba66"),
}
MARK = re.compile(r"\s*\[\d+\]$")


def csv_rows(path, version):
    rows = []
    with open(os.path.join(ROOT, path), newline="", encoding="utf-8") as f:
        for rec in csv.DictReader(f):
            reach = MARK.sub("", rec["Globally Reachable"].strip())
            for text in rec["Address Block"].split(","):
                text = MARK.sub("", text.strip())
                net = ipaddress.ip_network(text, strict=True)
                if net.version != version:
                    raise SystemExit(f"{path}: {text} is not IPv{version}")
                rows.append((text, int(net.network_address), net.prefixlen, reach, rec["Name"]))
    return rows


def lean_rows():
    out = subprocess.run(["lake", "env", "lean", "scripts/Registry.lean"], cwd=ROOT, check=True,
                         capture_output=True, text=True).stdout
    rows = {"ROW4": [], "ROW6": []}
    for line in out.splitlines():
        kind, text, base, length, reach, name = line.split("|", 5)
        rows[kind].append((text, int(base), int(length), reach, name))
    return rows


def main():
    failures = []
    lean = lean_rows()
    counts = []
    for kind, (path, version, sha) in FILES.items():
        with open(os.path.join(ROOT, path), "rb") as f:
            digest = hashlib.sha256(f.read()).hexdigest()
        if digest != sha:
            failures.append(f"{path}: SHA-256 {digest}, expected {sha}")
        want = csv_rows(path, version)
        got = lean[kind]
        if len(want) != len(got):
            failures.append(f"{path}: {len(want)} rows in the CSV file, {len(got)} in Lean")
        for i, (w, g) in enumerate(zip(want, got)):
            if w[1:] != g[1:]:
                failures.append(f"{path} row {i}: CSV {w!r}, Lean {g!r}")
            elif w[0] != g[0]:
                failures.append(f"{path} row {i}: CSV writes {w[0]}, URLFence prints {g[0]}")
        counts.append(f"{len(got)} IPv{version} rows")
    for f in failures:
        print("check_registry:", f, file=sys.stderr)
    if failures:
        sys.exit(1)
    print(f"check_registry: OK ({', '.join(counts)} equal to the CSV files; blocks, lengths, "
          "Globally Reachable values, names and printed blocks)")


if __name__ == "__main__":
    main()
