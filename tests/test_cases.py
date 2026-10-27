"""Fixed cases: inputs in the style of published URL-allowlist bugs, and the CLI's contract."""
import subprocess
import unittest

from common import BIN, run_check, run_raw

ALLOW = ["docs.python.org", "*.example.com", "127.0.0.1"]

CASES = [
    # (url, decision, host or reason)
    # Prefix-matched lookalikes (CVE-2026-24052, CVE-2026-46341 style) are other hosts.
    ("https://docs.python.org.evil.com/3/", "deny", "docs.python.org.evil.com"),
    ("https://docs.python.org/3/", "allow", "docs.python.org"),
    # Userinfo (CVE-2025-47241, CVE-2026-46341 style) is refused.
    ("https://docs.python.org@evil.com/", "reject", "userinfo"),
    ("https://docs.python.org:pass@localhost:8080/", "reject", "userinfo"),
    # Suffix without the dot (CVE-2026-33393 style).
    ("https://attacker-example.com/", "deny", "attacker-example.com"),
    ("https://a.b.example.com/", "allow", "a.b.example.com"),
    ("https://example.com/", "deny", "example.com"),
    # Percent-encoded delimiters (CVE-2026-6322 style), backslashes, whitespace.
    ("https://docs.python.org%40evil.com/", "reject", "percent"),
    ("https://evil.com\\@docs.python.org/", "reject", "chars"),
    ("https://docs.python.org\t.evil.com/", "reject", "chars"),
    (" https://docs.python.org/", "reject", "chars"),
    # IP literals: only the four-part decimal form; no IPv6 (CVE-2026-49857 style).
    ("https://127.0.0.1/", "allow", "127.0.0.1"),
    ("https://127.1/", "reject", "host"),
    ("https://0x7f.0.0.1/", "reject", "host"),
    ("https://2130706433/", "reject", "host"),
    ("https://[::ffff:127.0.0.1]/", "reject", "ipv6"),
    ("https://a.b.example.123/", "reject", "host"),
    # Strict form only.
    ("HTTPS://docs.python.org/", "reject", "scheme"),
    ("https://Docs.python.org/", "reject", "host"),
    ("https:/docs.python.org/", "reject", "scheme"),
    ("https:docs.python.org", "reject", "scheme"),
    ("https://docs.python.org./", "reject", "host"),
    ("https://docs.python.org:/", "reject", "port"),
    ("https://docs.python.org:65536/", "reject", "port"),
    ("https://docs.python.org:8443/a?b#c", "allow", "docs.python.org"),
    ("https://bücher.example.com/", "reject", "chars"),
    ("", "reject", "scheme"),
    # The path, query and fragment never change the host.
    ("https://docs.python.org/@evil.com", "allow", "docs.python.org"),
    ("https://docs.python.org#@evil.com", "allow", "docs.python.org"),
    ("https://docs.python.org?next=https://evil.com", "allow", "docs.python.org"),
    # Only https by default.
    ("http://docs.python.org/", "deny", "docs.python.org"),
]


def detail(r):
    return r.get("host", r.get("reason"))


class FixedCases(unittest.TestCase):
    def test_cases(self):
        _, out = run_check([u for u, _, _ in CASES], ALLOW, stdin=True)
        self.assertEqual(len(out), len(CASES))
        for (url, decision, d), r in zip(CASES, out):
            with self.subTest(url=url):
                self.assertEqual((r["input"], r["decision"], detail(r)), (url, decision, d))

    def test_deny_wins_and_schemes(self):
        _, out = run_check(["https://evil.example.com/", "https://ok.example.com/"], ["*.example.com"],
                           ["evil.example.com"])
        self.assertEqual([r["decision"] for r in out], ["deny", "allow"])
        status, out = run_check(["http://docs.python.org/"], ["docs.python.org"], schemes=["http"])
        self.assertEqual((status, out[0]["decision"]), (0, "allow"))

    def test_port_and_fields(self):
        _, out = run_check(["https://docs.python.org:8443/x"], ALLOW)
        self.assertEqual(out[0], {"input": "https://docs.python.org:8443/x", "decision": "allow",
                                  "scheme": "https", "host": "docs.python.org", "port": "8443"})

    def test_encoding_and_ascii_output(self):
        status, out = run_raw(["check", "--allow", "docs.python.org", "--stdin"],
                              b"https://docs.python.org/\nhttps://x\xff/\nhttps://\xe2\x80\xa8/\n")
        self.assertEqual([r["decision"] for r in out], ["allow", "reject", "reject"])
        self.assertEqual([r.get("reason") for r in out], [None, "encoding", "chars"])
        self.assertEqual(out[1]["input_hex"], "68747470733a2f2f78ff2f")
        raw = subprocess.run([BIN, "check", "--allow", "docs.python.org", "--", "https:// /"],
                             capture_output=True, check=False).stdout
        self.assertTrue(raw.isascii())
        self.assertEqual(len(raw.decode().splitlines()), 1)

    def test_usage_errors(self):
        self.assertEqual(run_raw(["check", "--", "https://docs.python.org/"])[0], 2)  # no --allow
        self.assertEqual(run_raw(["check", "--allow", "docs.python.org"])[0], 2)  # no URLs
        self.assertEqual(run_raw(["check", "--allow", "docs.python.org", "--stdin"], b"")[0], 2)
        self.assertEqual(run_raw(["check", "--allow", "docs.python.org", "https://docs.python.org/"])[0], 2)
        for bad in ["Docs.python.org", "*", "*.127.0.0.1", "docs.python.org.", "", "https://x"]:
            with self.subTest(pattern=bad):
                self.assertEqual(run_raw(["check", "--allow", bad, "--", "https://x/"])[0], 2)
        self.assertEqual(run_raw(["check", "--allow", "x.org", "--scheme", "ftp", "--", "https://x.org/"])[0], 2)
        # After `--`, option names are URLs (and are rejected as such).
        status, out = run_raw(["check", "--allow", "docs.python.org", "--", "--stdin"])
        self.assertEqual((status, out[0]["decision"], out[0]["reason"]), (1, "reject", "scheme"))


if __name__ == "__main__":
    unittest.main()
