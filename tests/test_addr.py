"""`urlfence addr`: the registry tables against the IANA files, the address parser against Python's
`socket.inet_pton` and `ipaddress` on about 50,000 strings, the decisions against
`ipaddress.is_global` with every difference listed and explained, and the CLI's contract.

    python3 tests/test_addr.py --table    # print the parser counts and the is_global comparison

The parser comparison needs glibc's `inet_pton` (Linux; other C libraries read some forms
differently) and Python 3.9.5 or later (earlier `ipaddress` accepts IPv4 parts with leading zeros).
How many decisions differ from `is_global` depends on the Python version, whose table of special
blocks changes between releases; every difference must still be explained below.
"""
import csv
import ipaddress
import os
import random
import re
import shutil
import socket
import subprocess
import sys
import unittest

from common import BIN, ROOT, run_raw

MARK = re.compile(r"\s*\[\d+\]$")


def run_addr(addrs, options=(), stdin=True):
    """(exit status, results) of `urlfence addr` for these addresses."""
    if stdin:
        return run_raw(["addr", *options, "--stdin"], "".join(a + "\n" for a in addrs).encode())
    return run_raw(["addr", *options, "--", *addrs])


# ---- (a) the registry tables -----------------------------------------------------------------------

class Registry(unittest.TestCase):
    def test_lean_tables_equal_the_iana_files(self):
        if shutil.which("lake") is None:
            self.skipTest("lake is not installed")
        p = subprocess.run([sys.executable, os.path.join(ROOT, "scripts", "check_registry.py")],
                           capture_output=True, text=True, check=False)
        self.assertEqual(p.returncode, 0, p.stdout + p.stderr)


# ---- (b) the parser against inet_pton and ipaddress ------------------------------------------------

def corpus(n=50_000, seed=20261028):
    """Deterministic strings near and inside the IPv4 and IPv6 text forms, and random ones."""
    rnd = random.Random(seed)
    alphabet = "0123456789abcdefABCDEFxg:.%/[] "
    special6 = [0, 0x64, 0x100, 0x2001, 0x2002, 0x2606, 0x3fff, 0x5f00, 0xfc00, 0xfd00, 0xfe80, 0xfec0, 0xff02]

    def groups():
        if rnd.random() < 0.3:
            g = [0] * 8
            for i in rnd.sample(range(8), rnd.randrange(0, 4)):
                g[i] = rnd.choice([1, 0xffff, rnd.randrange(65536)])
        else:
            g = [rnd.choice([0, 0, 0, 1, 0xffff, rnd.randrange(65536), rnd.randrange(16)]) for _ in range(8)]
        if rnd.random() < 0.4:
            g[0] = rnd.choice(special6)
        if rnd.random() < 0.15:
            g[:6] = [0, 0, 0, 0, 0, 0xffff]
        return g

    def hexg(x):
        s = rnd.choice(["%x", "%04x", "%X", "%02x"]) % x
        return s if len(s) <= 4 else "%x" % x

    def text6(g):
        form = rnd.randrange(5)
        if form == 0:  # full
            return ":".join(hexg(x) for x in g)
        if form == 1:  # one zero run of any length (or none) replaced by ::
            i = rnd.randrange(9)
            j = rnd.randrange(i, 9)
            if any(g[i:j]):
                return ":".join(hexg(x) for x in g)
            return ":".join(hexg(x) for x in g[:i]) + "::" + ":".join(hexg(x) for x in g[j:])
        if form == 2:  # Python's compressed form
            return ipaddress.IPv6Address(bytes(b for x in g for b in x.to_bytes(2, "big"))).compressed
        quad = ".".join(str(b) for x in g[6:] for b in x.to_bytes(2, "big"))
        if form == 3:
            return ":".join(hexg(x) for x in g[:6]) + ":" + quad
        i = rnd.randrange(7)
        j = rnd.randrange(i, 7)
        if any(g[i:j]):
            return ":".join(hexg(x) for x in g[:6]) + ":" + quad
        head = ":".join(hexg(x) for x in g[:i]) + "::" + ":".join(hexg(x) for x in g[j:6])
        return head + ("" if head.endswith(":") else ":") + quad

    def text4():
        b = [rnd.choice([0, 1, 10, 127, 169, 172, 192, 224, 255, rnd.randrange(256)]) for _ in range(4)]
        form = rnd.randrange(6)
        if form < 3:
            return ".".join(map(str, b))
        if form == 3:
            return ".".join(rnd.choice(["%d", "%03d", "0x%x", "%o"]) % x for x in b)
        if form == 4:
            return ".".join(map(str, b[:rnd.randrange(1, 4)]))
        return str(int.from_bytes(bytes(b), "big"))

    def mutate(s):
        for _ in range(rnd.randrange(1, 3)):
            k, i = rnd.randrange(6), rnd.randrange(len(s) + 1)
            if k == 0:
                s = s[:i] + rnd.choice(alphabet) + s[i:]
            elif k == 1 and s:
                s = s[:i] + s[i + 1:]
            elif k == 2 and s:
                s = s[:i] + rnd.choice(alphabet) + s[i + 1:]
            elif k == 3:
                s = s + rnd.choice(["%eth0", "%25", "/64", "/128", ":", "::", ".0", " "])
            elif k == 4:
                s = "[" + s + "]"
            else:
                s = s.replace("::", ":::", 1) if "::" in s else s + "::1"
        return s

    out = []
    while len(out) < n:
        r = rnd.random()
        s = text6(groups()) if r < 0.45 else text4() if r < 0.65 else None
        if s is None:
            s = rnd.choice([text6(groups()), text4()]) if r < 0.9 else \
                "".join(rnd.choice(alphabet) for _ in range(rnd.randrange(0, 46)))
            if r < 0.9:
                s = mutate(s)
        out.append(s)
    return out


def inet_pton(s):
    try:
        return socket.inet_pton(socket.AF_INET6 if ":" in s else socket.AF_INET, s)
    except OSError:
        return None


def ip_packed(s):
    try:
        return ipaddress.ip_address(s).packed
    except ValueError:
        return None


def why_rejected(s):
    """The category of a string URLFence refuses."""
    checks = [
        ("zone ID", "%" in s), ("brackets", "[" in s or "]" in s), ("prefix length", "/" in s),
        ("space", " " in s), ("not hex", re.search(r"[^0-9a-fA-F:.]", s) is not None), ("empty", s == ""),
        ("more than one ::", s.count("::") > 1 or ":::" in s),
    ]
    for name, hit in checks:
        if hit:
            return name
    if ":" not in s:
        parts = s.split(".")
        if len(parts) != 4:
            return "IPv4 without four parts"
        if any(len(p) > 1 and p[0] == "0" for p in parts if p):
            return "IPv4 part with a leading zero"
        return "IPv4 part not 0 to 255"
    if "." in s:
        return "bad dotted quad in IPv6"
    return "bad IPv6 groups"


def differential(strings):
    """Compare `urlfence addr` with inet_pton and ipaddress on `strings`: (accepted, printed forms
    compared with ipaddress, rejected strings by category, problems)."""
    _, out = run_addr(strings)
    if len(out) != len(strings):
        return 0, 0, {}, [f"{len(out)} results for {len(strings)} strings"]
    accepted, text_checked, rejected, problems = 0, 0, {}, []
    for s, r in zip(strings, out):
        pton, packed = inet_pton(s), ip_packed(s)
        if r.get("input") != s:
            problems.append(f"answer for something else: {s!r} {r!r}")
        elif r["decision"] == "reject":
            cat = why_rejected(s)
            rejected[cat] = rejected.get(cat, 0) + 1
            if r.get("reason") != "parse":
                problems.append(f"reject without reason parse: {s!r} {r!r}")
            # inet_pton reads the same forms: a string it accepts must not be refused.
            if pton is not None:
                problems.append(f"refused, but inet_pton reads it: {s!r}")
            # ipaddress also accepts a zone ID on IPv6 addresses; nothing else may differ.
            if packed is not None and "%" not in s:
                problems.append(f"refused, but ipaddress reads it: {s!r}")
        else:
            accepted += 1
            if r.get("family") != ("ipv6" if ":" in s else "ipv4"):
                problems.append(f"family: {s!r} {r!r}")
            if pton is None or pton != packed or inet_pton(r.get("addr", "")) != pton:
                problems.append(f"accepted as {r.get('addr')!r}, inet_pton {pton!r}, ipaddress {packed!r}: {s!r}")
                continue
            py = str(ipaddress.ip_address(s))
            if "." not in py or r["family"] == "ipv4":  # newer Pythons print IPv4-mapped addresses mixed
                text_checked += 1
                if r["addr"] != py:
                    problems.append(f"printed {r['addr']!r}, ipaddress prints {py!r}: {s!r}")
    return accepted, text_checked, rejected, problems


class Parser(unittest.TestCase):
    def test_agrees_with_inet_pton_and_ipaddress(self):
        accepted, text_checked, rejected, problems = differential(corpus())
        self.assertEqual(problems[:20], [])
        self.assertGreater(accepted, 15_000)
        self.assertGreater(text_checked, accepted * 0.9)
        self.assertGreater(sum(rejected.values()), 15_000)
        for cat in ("zone ID", "brackets", "prefix length", "IPv4 part with a leading zero", "IPv4 without four parts",
                    "more than one ::", "bad IPv6 groups", "bad dotted quad in IPv6"):
            self.assertGreater(rejected.get(cat, 0), 0, cat)


# ---- (c) the decisions against ipaddress.is_global -------------------------------------------------

def net(s):
    return ipaddress.ip_network(s)


# Every address where URLFence's decision (allowed or not) differs from `is_global`, by the first
# rule that explains it. All of them are addresses URLFence denies and `is_global` calls global.
EXPLAINED = [
    ("192.0.0.0/24 is denied as a whole; IANA marks 192.0.0.9 and 192.0.0.10 (PCP, TURN anycast) True",
     lambda a, r: a in net("192.0.0.0/24")),
    ("rows with an empty Globally Reachable value are denied: 192.88.99.0/24 (6to4 relay anycast, terminated)",
     lambda a, r: a in net("192.88.99.0/24")),
    ("IPv4 multicast 224.0.0.0/4 is denied; it is not in the special-purpose registry",
     lambda a, r: a in net("224.0.0.0/4")),
    ("2001::/23 is denied as a whole, including the rows IANA marks True (2001:1::1-3, 2001:3::/32, "
     "2001:4:112::/48, 2001:20::/28, 2001:30::/28)",
     lambda a, r: a in net("2001::/23")),
    ("3fff::/20 (documentation, RFC 9637, 2024) is a registry row this Python does not know",
     lambda a, r: a in net("3fff::/20")),
    ("64:ff9b::/96 (well-known NAT64, IANA True) is denied unless configured with --nat64, and then "
     "decided on the IPv4 address it carries",
     lambda a, r: a in net("64:ff9b::/96")),
    ("5f00::/16 (SRv6 SIDs, RFC 9602, 2024) is a registry row this Python does not know; outside 2000::/3",
     lambda a, r: a in net("5f00::/16")),
    ("100:0:0:1::/64 (dummy prefix, RFC 9780, 2025) is a registry row this Python does not know",
     lambda a, r: a in net("100:0:0:1::/64")),
    ("::/96 holds the deprecated IPv4-compatible addresses; outside 2000::/3, denied",
     lambda a, r: a in net("::/96")),
    ("fec0::/10 (site-local, deprecated by RFC 3879) is outside 2000::/3, denied",
     lambda a, r: a in net("fec0::/10")),
    ("ff00::/8 (IPv6 multicast) is outside 2000::/3, denied",
     lambda a, r: a in net("ff00::/8")),
    ("other IPv6 space outside 2000::/3 is not allocated as global unicast: denied",
     lambda a, r: a.version == 6 and a not in net("2000::/3") and a not in net("::ffff:0:0/96")),
    ("an ISATAP interface identifier carries a denied IPv4 address; ipaddress does not decode ISATAP",
     lambda a, r: r.get("reason", "").startswith("isatap ")),
    ("an IPv4-mapped address of an IPv4 address that is not globally reachable (100.64.0.0/10) or "
     "multicast; is_global here only asks whether the IPv4 address is private",
     lambda a, r: a in net("::ffff:0:0/96") and r.get("reason", "").startswith("mapped ")),
    ("2002::/16 (6to4, N/A) is denied as a whole; Pythons before the CVE-2024-4032 update of ipaddress "
     "do not list it",
     lambda a, r: a in net("2002::/16")),
    ("any other registry row that is not globally reachable and that this Python's table does not list",
     lambda a, r: r.get("reason", "").startswith("registry ")),
]


def probes():
    """The first and last address of every registry block and the addresses just outside them, the
    edges of 2000::/3 and 224.0.0.0/4, and the IPv6 forms that carry an IPv4 address."""
    out = []
    for name in ("iana-ipv4-special-registry.csv", "iana-ipv6-special-registry.csv"):
        with open(os.path.join(ROOT, "data", name), newline="", encoding="utf-8") as f:
            for rec in csv.DictReader(f):
                for b in rec["Address Block"].split(","):
                    n = net(MARK.sub("", b.strip()))
                    first, last = int(n.network_address), int(n.broadcast_address)
                    for x in (first - 1, first, first + 1, (first + last) // 2, last, last + 1):
                        if 0 <= x < 2 ** n.max_prefixlen:
                            out.append(str(ipaddress.ip_address(x) if n.version == 4 else ipaddress.IPv6Address(x)))
    out += ["223.255.255.255", "224.0.0.0", "239.255.255.255", "8.8.8.8", "1.1.1.1",
            "1fff:ffff:ffff:ffff:ffff:ffff:ffff:ffff", "2000::", "3fff:ffff:ffff:ffff:ffff:ffff:ffff:ffff",
            "4000::", "fec0::1", "ff02::1", "ff0e::1", "2606:4700:4700::1111"]
    for v in ("127.0.0.1", "10.0.0.1", "169.254.169.254", "100.100.100.200", "192.0.0.192", "224.0.0.1",
              "8.8.8.8", "1.1.1.1", "192.31.196.1"):
        h = ipaddress.IPv4Address(v).packed.hex()
        g = f"{int(h[:4], 16):x}:{int(h[4:], 16):x}"
        out += [f"::ffff:{v}", f"::{v}", f"64:ff9b::{v}", f"64:ff9b:1::{v}", f"2002:{g}::1",
                f"2001:0:4136:e378:8000:63bf:{g}", f"2606:4700::5efe:{v}", f"2606:4700::200:5efe:{v}",
                f"2606:4700:64::{v}", f"fec0::{v}"]
    return list(dict.fromkeys(out))


def comparison():
    """(address, URLFence's result, is_global, is_private, explanation or None) for every probe whose
    decision differs from is_global."""
    addrs = probes()
    _, out = run_addr(addrs)
    rows = []
    for s, r in zip(addrs, out):
        a = ipaddress.ip_address(s)
        if (r["decision"] == "allow") != a.is_global:
            why = next((name for name, hit in EXPLAINED if r["decision"] == "deny" and hit(a, r)), None)
            rows.append((s, r, a.is_global, a.is_private, why))
    return addrs, rows


class IsGlobal(unittest.TestCase):
    def test_every_difference_is_explained(self):
        addrs, rows = comparison()
        self.assertGreater(len(addrs), 250)
        unexplained = [(s, r["decision"], r.get("reason"), g) for s, r, g, _, why in rows if why is None]
        self.assertEqual(unexplained, [])

    def test_agreement_where_it_matters(self):
        # The rows of the registry that are globally reachable, outside the blocks denied as a whole.
        _, out = run_addr(["192.31.196.1", "192.52.193.1", "192.175.48.1", "2620:4f:8000::1",
                           "::ffff:8.8.8.8", "8.8.8.8", "2606:4700:4700::1111"])
        self.assertEqual([r["decision"] for r in out], ["allow"] * 7)


# ---- (d) the CLI's contract ------------------------------------------------------------------------

class Contract(unittest.TestCase):
    def test_fields(self):
        status, out = run_addr(["8.8.8.8", "::ffff:127.0.0.1", "fe80::1%eth0"], stdin=False)
        self.assertEqual(status, 1)
        self.assertEqual(out, [
            {"input": "8.8.8.8", "decision": "allow", "family": "ipv4", "addr": "8.8.8.8"},
            {"input": "::ffff:127.0.0.1", "decision": "deny", "family": "ipv6", "addr": "::ffff:7f00:1",
             "reason": "mapped 127.0.0.1: registry 127.0.0.0/8 Loopback"},
            {"input": "fe80::1%eth0", "decision": "reject", "reason": "parse"}])

    def test_exit_status(self):
        self.assertEqual(run_addr(["8.8.8.8", "2606:4700:4700::1111"])[0], 0)
        self.assertEqual(run_addr(["8.8.8.8", "10.0.0.1"])[0], 1)
        self.assertEqual(run_addr(["8.8.8.8", "8.8.8"])[0], 1)

    def test_reasons(self):
        cases = [
            ("169.254.169.254", [], "registry 169.254.0.0/16 Link Local"),
            ("100.100.100.200", [], "registry 100.64.0.0/10 Shared Address Space"),
            ("192.0.0.192", [], "registry 192.0.0.0/24 IETF Protocol Assignments"),
            ("fd00:ec2::254", [], "outside 2000::/3"),
            ("224.0.0.251", [], "multicast 224.0.0.0/4"),
            ("2002:7f00:1::", [], "registry 2002::/16 6to4"),
            ("2001:0:4136:e378:8000:63bf:3fff:fdd2", [], "registry 2001::/23 IETF Protocol Assignments"),
            ("3fff::1", [], "registry 3fff::/20 Documentation"),
            ("64:ff9b::a9fe:a9fe", [], "outside 2000::/3"),
            ("64:ff9b::a9fe:a9fe", ["--nat64", "64:ff9b::/96"],
             "nat64-embedded 169.254.169.254: registry 169.254.0.0/16 Link Local"),
            ("2606:4700::200:5efe:10.0.0.1", [], "isatap 10.0.0.1: registry 10.0.0.0/8 Private-Use"),
            ("8.8.4.4", ["--deny", "8.8.0.0/16"], "deny 8.8.0.0/16"),
            ("::ffff:8.8.4.4", ["--deny", "8.8.0.0/16"], "mapped 8.8.4.4: deny 8.8.0.0/16"),
            ("2606:4700:4700::1111", ["--deny", "2606:4700::/32"], "deny 2606:4700::/32"),
            ("0.0.0.0", [], 'registry 0.0.0.0/8 "This network"'),
        ]
        for addr, opts, reason in cases:
            with self.subTest(addr=addr, opts=opts):
                status, out = run_addr([addr], opts)
                self.assertEqual((status, out[0]["decision"], out[0]["reason"]), (1, "deny", reason))

    def test_nat64(self):
        status, out = run_addr(["64:ff9b::808:808", "64:ff9b::7f00:1", "64:ff9b:1::808:808"],
                               ["--nat64", "64:ff9b::/96"])
        self.assertEqual([r["decision"] for r in out], ["allow", "deny", "deny"])
        status, out = run_addr(["2606:4700:64::808:808", "2606:4700:64::a00:1"], ["--nat64", "2606:4700:64::/96"])
        self.assertEqual([r["decision"] for r in out], ["allow", "deny"])

    def test_usage_errors(self):
        def usage(*args, data=None):
            return run_raw(["addr", *args], data)[0]
        self.assertEqual(usage(), 2)
        self.assertEqual(usage("--stdin", data=b""), 2)
        self.assertEqual(usage("8.8.8.8"), 2)  # addresses go after `--`
        self.assertEqual(usage("--bogus", "--", "8.8.8.8"), 2)
        self.assertEqual(usage("--deny"), 2)
        self.assertEqual(usage("--nat64"), 2)
        for bad in ["10.0.0.1/8", "10.0.0.0/33", "10.0.0.0/08", "10.0.0.0", "10.0.0.0/", "/8", "::/129",
                    "[::]/0", "fe80::/10/1", "::1%lo/128", "10.0.0.0/8 ", "010.0.0.0/8"]:
            with self.subTest(deny=bad):
                self.assertEqual(usage("--deny", bad, "--", "8.8.8.8"), 2)
        # Not a /96, IPv4, or a prefix that nat64Ok would ignore: refused, never silently dropped.
        for bad in ["64:ff9b::/64", "64:ff9b::/97", "64:ff9b::1/96", "10.0.0.0/8", "64:ff9b:1::/96",
                    "2001:db8:64::/96", "fd00::/96", "2002::/96", "::ffff:0:0/96", "::/96", "4000::/96"]:
            with self.subTest(nat64=bad):
                self.assertEqual(usage("--nat64", bad, "--", "8.8.8.8"), 2)
        for good in ["64:ff9b::/96", "2606:4700:64::/96", "64:FF9B:0:0:0:0:0:0/96"]:
            with self.subTest(nat64=good):
                self.assertEqual(usage("--nat64", good, "--", "8.8.8.8"), 0)
        self.assertEqual(usage("--deny", "0.0.0.0/0", "--deny", "::/0", "--", "8.8.8.8"), 1)
        # After `--`, option names are addresses (and are rejected as such).
        status, out = run_raw(["addr", "--", "--stdin"])
        self.assertEqual((status, out[0]["decision"], out[0]["reason"]), (1, "reject", "parse"))

    def test_stdin_encoding_and_ascii_output(self):
        status, out = run_raw(["addr", "--stdin"], b"8.8.8.8\n\xff\n\xd9\xa1.2.3.4\n8.8.8.8\r\n")
        self.assertEqual([r["decision"] for r in out], ["allow", "reject", "reject", "reject"])
        self.assertEqual([r.get("reason") for r in out], [None, "encoding", "parse", "parse"])
        self.assertEqual(out[1]["input_hex"], "ff")
        raw = subprocess.run([BIN, "addr", "--", "١.2.3.4"], capture_output=True, check=False).stdout
        self.assertTrue(raw.isascii())
        self.assertIn(b"\\u0661", raw)

    def test_stdin_and_arguments_agree(self):
        strings = corpus(2_000, seed=7)
        self.assertEqual(run_addr(strings, stdin=True)[1], run_addr(strings, stdin=False)[1])


def print_table():
    strings = corpus()
    accepted, text_checked, rejected, problems = differential(strings)
    print(f"parser: {len(strings)} strings, {accepted} accepted ({text_checked} printed forms compared), "
          f"{sum(rejected.values())} refused, {len(problems)} problems")
    for cat, n in sorted(rejected.items(), key=lambda x: -x[1]):
        print(f"{n:6}  refused: {cat}")
    print()
    addrs, rows = comparison()
    print(f"{len(addrs)} addresses, {len(rows)} where URLFence's decision differs from is_global "
          f"(Python {sys.version.split()[0]})")
    counts = {}
    for s, r, g, p, why in rows:
        counts[why] = counts.get(why, 0) + 1
        print(f"{s:42} {r['decision']:5} is_global={g!s:5} is_private={p!s:5} {r.get('reason', '')}")
    print()
    for why, n in counts.items():
        print(f"{n:4}  {why}")


if __name__ == "__main__":
    if sys.argv[1:] == ["--table"]:
        print_table()
    else:
        unittest.main()
