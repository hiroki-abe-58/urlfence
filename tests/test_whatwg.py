"""Random and adversarial URLs: whenever URLFence accepts a URL, the WHATWG URL parser (Node's `URL`)
must read the same scheme, host and port, with no userinfo, and the decision must be what the
matching rules give for that host. URLFence may refuse URLs that WHATWG accepts (it fails closed);
the test counts those but does not fail on them.
"""
import random
import unittest

from common import NODE, model_decision, run_check, whatwg

SCHEMES = ["https://", "http://", "HTTPS://", "https:/", "https:///", "https:", "ftp://", "https:\\\\",
           "javascript:", "https://", "https://"]
HOSTS = ["example.com", "docs.example.com", "a.b.example.com", "attacker-example.com", "example.com.evil.net",
         "evil.com", "127.0.0.1", "127.1", "0x7f.0.0.1", "017.0.0.1", "192.168.0.1", "256.0.0.1", "1.2.3",
         "example.123", "foo.0x7f", "Example.com", "xn--bcher-kva.example", "bücher.example", "a_b.example.com",
         "-a.example.com", "a-.example.com", "example.com.", ".example.com", "localhost", "[::1]",
         "[::ffff:127.0.0.1]", "example.com%2eevil.com", "a" * 64 + ".com", "1.example.com"]
AUTH_EXTRA = ["", "", "", ":443", ":8443", ":", ":08443", ":99999", "@evil.com", ":pass@evil.com",
              "%40evil.com", "\\@evil.com", "\t.evil.com", " ", "#@evil.com", "?@evil.com", ".evil.com"]
RESTS = ["", "/", "/a/b", "/a?b#c", "?x=//evil.com", "#frag", "/@evil.com", "/..%2f", "/é"]

ALLOW = ["example.com", "*.example.com", "127.0.0.1", "localhost"]
DENY = ["evil.example.com"]


VALID_HOSTS = ["example.com", "docs.example.com", "a.b.example.com", "evil.example.com", "attacker-example.com",
               "example.com.evil.net", "evil.com", "127.0.0.1", "192.168.0.1", "localhost", "1.example.com"]


def random_url(rng):
    if rng.random() < 0.6:
        # Mostly well-formed, so that allow and deny both occur often.
        return (rng.choice(["https://", "http://"]) + rng.choice(VALID_HOSTS) +
                rng.choice(["", "", ":443", ":8443", ":80"]) + rng.choice(RESTS))
    return rng.choice(SCHEMES) + rng.choice(HOSTS) + rng.choice(AUTH_EXTRA) + rng.choice(RESTS)


@unittest.skipIf(NODE is None, "node is not installed")
class AgainstWhatwg(unittest.TestCase):
    def test_accepted_urls_mean_the_same_to_whatwg(self):
        rng = random.Random(20261027)
        urls = sorted({random_url(rng) for _ in range(20000)})
        for schemes in (["https"], ["http", "https"]):
            _, out = run_check(urls, ALLOW, DENY, schemes=schemes, stdin=True)
            ref = whatwg(urls)
            self.assertEqual(len(out), len(urls))
            counts = {"allow": 0, "deny": 0, "reject": 0, "whatwg_only": 0}
            for u, r, w in zip(urls, out, ref):
                with self.subTest(url=u, schemes=schemes):
                    counts[r["decision"]] += 1
                    if r["decision"] == "reject":
                        counts["whatwg_only"] += w["ok"]
                        continue
                    self.assertTrue(w["ok"], "URLFence accepted a URL that WHATWG rejects")
                    self.assertEqual(w["protocol"], r["scheme"] + ":")
                    self.assertEqual(w["hostname"], r["host"])
                    self.assertEqual((w["username"], w["password"]), ("", ""))
                    default = {"http": "80", "https": "443"}[r["scheme"]]
                    self.assertEqual(w["port"], "" if r["port"] in (None, default) else r["port"])
                    self.assertEqual(r["decision"], model_decision(w["hostname"], r["scheme"], ALLOW, DENY, schemes))
            # Every decision must occur often, or the comparison says little.
            for k in ("allow", "deny", "reject"):
                self.assertGreater(counts[k], 200, counts)
            print(f"\n  schemes={schemes}: {counts}", flush=True)


if __name__ == "__main__":
    unittest.main()
