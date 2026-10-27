import UrlFence.Api

/-!
# Examples, checked at build time

The first groups follow published bugs in URL allowlist checks:

* CVE-2026-24052 (Claude Code before 1.0.111) and CVE-2026-46341 (Apify MCP server before 0.9.21):
  the check was a string prefix, so `modelcontextprotocol.io.example.com` and `docs.apify.com@evil.com`
  passed;
* CVE-2026-33393 (Discourse): a suffix test without the dot, so `attacker-example.com` passed;
* CVE-2025-47241 (browser-use before 0.1.45): userinfo in the authority;
* CVE-2026-6322 (fast-uri before 3.1.2): a percent-encoded `@` in the host;
* CVE-2026-49857 (auth-fetch-mcp before 3.0.2): an IPv4-mapped IPv6 loopback address.

They show what URLFence decides for those inputs. They do not reproduce the original programs.
-/

namespace UrlFence.Examples
open UrlFence

/-- The decision for `s` under an https-only policy, as a short string. A pattern that does not
parse gives "bad policy", so no example can pass against an accidentally empty policy. -/
def decide1 (allow : List String) (s : String) : String :=
  match Policy.make ["https"] allow [] with
  | none => "bad policy"
  | some pol =>
    match pol.checkString s with
    | .allow u => "allow " ++ u.host.toString
    | .deny u => "deny " ++ u.host.toString
    | .reject r => "reject " ++ reprStr r

-- Prefix-matched lookalikes are other hosts.
#guard decide1 ["modelcontextprotocol.io"] "https://modelcontextprotocol.io.example.com/x" = "deny modelcontextprotocol.io.example.com"
#guard decide1 ["docs.apify.com"] "https://docs.apify.com.evil.com/payload" = "deny docs.apify.com.evil.com"
#guard decide1 ["docs.apify.com"] "https://docs.apify.com/x" = "allow docs.apify.com"
-- Userinfo is refused outright.
#guard decide1 ["docs.apify.com"] "https://docs.apify.com@evil.com/payload" = "reject UrlFence.Reason.userinfo"
#guard decide1 ["example.com"] "https://example.com:pass@localhost:8080" = "reject UrlFence.Reason.userinfo"
-- A suffix needs the dot.
#guard decide1 ["*.example.com"] "https://attacker-example.com/" = "deny attacker-example.com"
#guard decide1 ["*.example.com"] "https://docs.example.com/" = "allow docs.example.com"
#guard decide1 ["*.example.com"] "https://example.com/" = "deny example.com"
#guard decide1 ["*.example.com", "example.com"] "https://example.com/" = "allow example.com"
-- Percent signs, backslashes, whitespace and IPv6 literals in the authority are refused.
#guard decide1 ["trusted.com"] "https://trusted.com%40evil.com/" = "reject UrlFence.Reason.percent"
#guard decide1 ["good.com"] "https://evil.com\\@good.com/" = "reject UrlFence.Reason.chars"
#guard decide1 ["good.com"] "https://good.com\t.evil.com/" = "reject UrlFence.Reason.chars"
#guard decide1 ["localhost"] "https://[::ffff:127.0.0.1]/" = "reject UrlFence.Reason.ipv6"
-- Number-like hosts that WHATWG reads as IPv4 are refused unless written as four decimal parts.
#guard decide1 ["127.0.0.1"] "https://127.0.0.1/" = "allow 127.0.0.1"
#guard decide1 ["127.0.0.1"] "https://127.1/" = "reject UrlFence.Reason.host"
#guard decide1 ["127.0.0.1"] "https://0x7f.0.0.1/" = "reject UrlFence.Reason.host"
#guard decide1 ["127.0.0.1"] "https://017.0.0.1/" = "reject UrlFence.Reason.host"
#guard decide1 ["example.com"] "https://example.123/" = "reject UrlFence.Reason.host"
#guard decide1 ["example.com"] "https://foo.0x7f/" = "reject UrlFence.Reason.host"
-- Only the strict form: lowercase scheme and host, `//`, no trailing dot, no empty port.
#guard decide1 ["example.com"] "HTTPS://example.com/" = "reject UrlFence.Reason.scheme"
#guard decide1 ["example.com"] "https://Example.com/" = "reject UrlFence.Reason.host"
#guard decide1 ["example.com"] "https:/example.com/" = "reject UrlFence.Reason.scheme"
#guard decide1 ["example.com"] "https:///example.com/" = "reject UrlFence.Reason.host"
#guard decide1 ["example.com"] "https://example.com./" = "reject UrlFence.Reason.host"
#guard decide1 ["example.com"] "https://example.com:/" = "reject UrlFence.Reason.port"
#guard decide1 ["example.com"] "https://example.com:8443/a?b#c" = "allow example.com"
#guard decide1 ["example.com"] "https://example.com:08443/" = "reject UrlFence.Reason.port"
-- The path, query and fragment do not change the host.
#guard decide1 ["example.com"] "https://example.com/@evil.com" = "allow example.com"
#guard decide1 ["example.com"] "https://example.com#@evil.com" = "allow example.com"
#guard decide1 ["example.com"] "https://example.com?x=//evil.com" = "allow example.com"
-- The authority ends only at `/`, `?` or `#`; other punctuation is not a host character.
#guard decide1 ["example.com"] "https://example.com;.evil.com/" = "reject UrlFence.Reason.host"
#guard decide1 ["example.com"] "https://example.com!.evil.com/" = "reject UrlFence.Reason.host"
#guard decide1 ["example.com"] "https://example.com,evil.com/" = "reject UrlFence.Reason.host"
-- IDNA A-labels and port 0 are refused.
#guard decide1 ["*.com"] "https://xn--a.com/" = "reject UrlFence.Reason.host"
#guard decide1 ["example.com"] "https://example.com:0/" = "reject UrlFence.Reason.port"
#guard decide1 ["Example.com"] "https://example.com/" = "bad policy"
-- http is refused when only https is allowed.
#guard decide1 ["example.com"] "http://example.com/" = "deny example.com"
-- Patterns are strict too.
#guard parsePattern "*.example.com" = some (.sub [['e','x','a','m','p','l','e'], ['c','o','m']])
#guard parsePattern "*.127.0.0.1" = none
#guard parsePattern "Example.com" = none
#guard parsePattern "*" = none

end UrlFence.Examples
