import UrlFence.Addr.Explain

/-!
# Address examples, checked at build time

The first groups follow published bugs in checks of resolved addresses, where an IPv4 address
written in IPv6 got past a check of the IPv4 forms:

* CVE-2026-49857 (auth-fetch-mcp before 3.0.2), <https://www.cve.org/CVERecord?id=CVE-2026-49857>:
  IPv4-mapped loopback `::ffff:7f00:1`;
* CVE-2026-42449, <https://www.cve.org/CVERecord?id=CVE-2026-42449>: IPv4-mapped metadata address
  `[::ffff:169.254.169.254]`;
* CVE-2026-44430, <https://www.cve.org/CVERecord?id=CVE-2026-44430>: 6to4 (`2002::/16`), NAT64
  (`64:ff9b::/96`, `64:ff9b:1::/48`) and site-local (`fec0::/10`) addresses were not denied;
* CVE-2026-48782 (pydantic-ai), <https://github.com/advisories/GHSA-cg7w-rg45-pc59>:
  IPv4-compatible `::a.b.c.d`, `64:ff9b:1::/48` and ISATAP.

They show what `Config.check` decides for those inputs. They do not reproduce the original
programs. The cloud metadata addresses follow: 169.254.169.254, 100.100.100.200, 192.0.0.192 and
fd00:ec2::254. The last groups show what is not decoded (see `UrlFence.Addr.Check`).
-/

namespace UrlFence.Addr.Examples
open UrlFence.Addr

/-- The decision for `s`, as a short string with the printed address. -/
def verdict (cfg : Config) (s : String) : String :=
  match cfg.checkString s with
  | .allow a => "allow " ++ a.toString
  | .deny a => "deny " ++ a.toString
  | .reject => "reject"

/-- Nothing added to the registries. -/
def plain : Config := {}

/-- The well-known NAT64 prefix in use. -/
def withNat64 : Config := { nat64 := [ip6 [0x64, 0xff9b, 0, 0, 0, 0, 0, 0]] }

-- IPv4-mapped addresses get the decision of their IPv4 address (CVE-2026-49857, CVE-2026-42449).
#guard verdict plain "::ffff:7f00:1" = "deny ::ffff:7f00:1"
#guard verdict plain "::ffff:127.0.0.1" = "deny ::ffff:7f00:1"
#guard verdict plain "::FFFF:7F00:0001" = "deny ::ffff:7f00:1"
#guard verdict plain "::ffff:169.254.169.254" = "deny ::ffff:a9fe:a9fe"
#guard verdict plain "0:0:0:0:0:ffff:a9fe:a9fe" = "deny ::ffff:a9fe:a9fe"
#guard verdict plain "::ffff:8.8.8.8" = "allow ::ffff:808:808"
-- Brackets belong to URLs, not to addresses: they are refused, as are zone IDs and prefix lengths.
#guard verdict plain "[::ffff:169.254.169.254]" = "reject"
#guard verdict plain "fe80::1%eth0" = "reject"
#guard verdict plain "::1/128" = "reject"
-- 6to4, NAT64 and site-local (CVE-2026-44430).
#guard verdict plain "2002:7f00:1::" = "deny 2002:7f00:1::"
#guard verdict plain "2002:a9fe:a9fe::1" = "deny 2002:a9fe:a9fe::1"
#guard verdict plain "2002:808:808::1" = "deny 2002:808:808::1"
#guard verdict plain "64:ff9b::7f00:1" = "deny 64:ff9b::7f00:1"
#guard verdict plain "64:ff9b::808:808" = "deny 64:ff9b::808:808"
#guard verdict plain "64:ff9b:1::a9fe:a9fe" = "deny 64:ff9b:1::a9fe:a9fe"
#guard verdict plain "fec0::1" = "deny fec0::1"
-- With the well-known NAT64 prefix in use, its addresses get the decision of their IPv4 address;
-- 64:ff9b:1::/48 stays denied.
#guard verdict withNat64 "64:ff9b::7f00:1" = "deny 64:ff9b::7f00:1"
#guard verdict withNat64 "64:ff9b::169.254.169.254" = "deny 64:ff9b::a9fe:a9fe"
#guard verdict withNat64 "64:ff9b::808:808" = "allow 64:ff9b::808:808"
#guard verdict withNat64 "64:ff9b:1::808:808" = "deny 64:ff9b:1::808:808"
-- A configured NAT64 prefix in a block that is not globally reachable is ignored.
#guard verdict { nat64 := [ip6 [0x2001, 0xdb8, 0x64, 0, 0, 0, 0, 0]] } "2001:db8:64::808:808" =
  "deny 2001:db8:64::808:808"
-- IPv4-compatible addresses and ISATAP (CVE-2026-48782).
#guard verdict plain "::127.0.0.1" = "deny ::7f00:1"
#guard verdict plain "::8.8.8.8" = "deny ::808:808"
#guard verdict plain "2606:4700::5efe:7f00:1" = "deny 2606:4700::5efe:7f00:1"
#guard verdict plain "2606:4700::200:5efe:169.254.169.254" = "deny 2606:4700::200:5efe:a9fe:a9fe"
#guard verdict plain "2606:4700::5efe:808:808" = "allow 2606:4700::5efe:808:808"
-- ISATAP identifiers with the g bit (RFC 5214, section 6.1) too.
#guard verdict plain "2606:4700:1::100:5efe:7f00:1" = "deny 2606:4700:1:0:100:5efe:7f00:1"
#guard verdict plain "2606:4700:1::300:5efe:a9fe:a9fe" = "deny 2606:4700:1:0:300:5efe:a9fe:a9fe"
#guard verdict plain "2606:4700:1::400:5efe:7f00:1" = "allow 2606:4700:1:0:400:5efe:7f00:1"
-- Teredo and the rest of 2001::/23.
#guard verdict plain "2001:0:4136:e378:8000:63bf:3fff:fdd2" = "deny 2001:0:4136:e378:8000:63bf:3fff:fdd2"
#guard verdict plain "2001:1::1" = "deny 2001:1::1"
-- Cloud metadata addresses.
#guard verdict plain "169.254.169.254" = "deny 169.254.169.254"
#guard verdict plain "100.100.100.200" = "deny 100.100.100.200"
#guard verdict plain "192.0.0.192" = "deny 192.0.0.192"
#guard verdict plain "fd00:ec2::254" = "deny fd00:ec2::254"
-- Allowed controls.
#guard verdict plain "8.8.8.8" = "allow 8.8.8.8"
#guard verdict plain "2606:4700:4700::1111" = "allow 2606:4700:4700::1111"
#guard verdict plain "2606:4700:4700:0:0:0:0:1111" = "allow 2606:4700:4700::1111"
#guard verdict plain "192.31.196.1" = "allow 192.31.196.1"
#guard verdict plain "2620:4f:8000::1" = "allow 2620:4f:8000::1"
-- Stricter than the registry: all of 192.0.0.0/24 is denied.
#guard verdict plain "192.0.0.9" = "deny 192.0.0.9"
-- Other special blocks.
#guard verdict plain "127.0.0.1" = "deny 127.0.0.1"
#guard verdict plain "0.0.0.0" = "deny 0.0.0.0"
#guard verdict plain "10.1.2.3" = "deny 10.1.2.3"
#guard verdict plain "224.0.0.1" = "deny 224.0.0.1"
#guard verdict plain "255.255.255.255" = "deny 255.255.255.255"
#guard verdict plain "::1" = "deny ::1"
#guard verdict plain "::" = "deny ::"
#guard verdict plain "fe80::1" = "deny fe80::1"
#guard verdict plain "ff02::1" = "deny ff02::1"
#guard verdict plain "100::1" = "deny 100::1"
#guard verdict plain "5f00::1" = "deny 5f00::1"
#guard verdict plain "3fff::1" = "deny 3fff::1"
#guard verdict plain "2001:db8::1" = "deny 2001:db8::1"
-- Prefixes the caller denies, also through IPv6.
#guard verdict { deny4 := [⟨ip4 8 8 8 0, 24⟩] } "8.8.8.8" = "deny 8.8.8.8"
#guard verdict { deny4 := [⟨ip4 8 8 8 0, 24⟩] } "::ffff:8.8.8.8" = "deny ::ffff:808:808"
#guard verdict { deny4 := [⟨ip4 8 8 8 0, 24⟩] } "8.8.4.4" = "allow 8.8.4.4"
#guard verdict { deny6 := [⟨ip6 [0x2606, 0x4700, 0, 0, 0, 0, 0, 0], 32⟩] } "2606:4700:4700::1111" =
  "deny 2606:4700:4700::1111"
-- Only the strict text forms.
#guard verdict plain "127.1" = "reject"
#guard verdict plain "0x7f.0.0.1" = "reject"
#guard verdict plain "017.0.0.1" = "reject"
#guard verdict plain "::ffff:017.0.0.1" = "reject"
#guard verdict plain "1::2::3" = "reject"
#guard verdict plain "1:2:3:4:5:6:7:8:9" = "reject"
#guard verdict plain "12345::" = "reject"
#guard verdict plain " 8.8.8.8" = "reject"
#guard verdict plain "" = "reject"
-- RFC 5952: the first longest run of two or more zero groups becomes `::`.
#guard (parseString "2001:db8:0:0:1:0:0:1").map toString = some "2001:db8::1:0:0:1"
#guard (parseString "2001:db8:0:1:0:0:0:1").map toString = some "2001:db8:0:1::1"
#guard (parseString "2001:db8:0:1:1:1:1:1").map toString = some "2001:db8:0:1:1:1:1:1"
#guard (parseString "1:2:3:4:5:6:7::").map toString = some "1:2:3:4:5:6:7:0"

/-- The reason `explain` gives for `s`. -/
def why (cfg : Config) (s : String) : String :=
  match parseString s with
  | none => "reject"
  | some a =>
    match cfg.explain a with
    | none => "allowed"
    | some w => w.text

-- Reasons name the first rule that denies, and the IPv4 address inside an IPv6 one.
#guard why plain "127.0.0.1" = "registry 127.0.0.0/8 Loopback"
#guard why plain "0.0.0.0" = "registry 0.0.0.0/8 \"This network\""
#guard why plain "192.0.0.9" = "registry 192.0.0.0/24 IETF Protocol Assignments"
#guard why plain "224.0.0.1" = "multicast 224.0.0.0/4"
#guard why plain "::ffff:169.254.169.254" = "mapped 169.254.169.254: registry 169.254.0.0/16 Link Local"
#guard why withNat64 "64:ff9b::a00:1" = "nat64-embedded 10.0.0.1: registry 10.0.0.0/8 Private-Use"
#guard why plain "64:ff9b::a00:1" = "outside 2000::/3"
#guard why plain "2606:4700::200:5efe:a9fe:a9fe" =
  "isatap 169.254.169.254: registry 169.254.0.0/16 Link Local"
#guard why plain "2002:7f00:1::" = "registry 2002::/16 6to4"
#guard why plain "2001:0:4136:e378:8000:63bf:3fff:fdd2" = "registry 2001::/23 IETF Protocol Assignments"
#guard why { deny4 := [⟨ip4 8 8 8 0, 24⟩] } "::ffff:8.8.8.8" = "mapped 8.8.8.8: deny 8.8.8.0/24"
#guard why { deny6 := [⟨ip6 [0x2606, 0x4700, 0, 0, 0, 0, 0, 0], 32⟩] } "2606:4700:4700::1111" =
  "deny 2606:4700::/32"
#guard why plain "8.8.8.8" = "allowed"
#guard why plain "fe80::1%eth0" = "reject"
-- Not decoded: a network-specific NAT64 prefix that is not configured (here 10.0.0.1 in a /96, and
-- in an RFC 6052 /64 with the u octet), and 6rd. Such prefixes belong in `deny6`.
#guard verdict plain "2a00:1450:64::a00:1" = "allow 2a00:1450:64::a00:1"
#guard verdict { nat64 := [ip6 [0x2a00, 0x1450, 0x64, 0, 0, 0, 0, 0]] } "2a00:1450:64::a00:1" =
  "deny 2a00:1450:64::a00:1"
#guard verdict plain "2a00:1450:4001:64:a:0:100:0" = "allow 2a00:1450:4001:64:a:0:100:0"
#guard verdict { deny6 := [⟨ip6 [0x2a00, 0x1450, 0x4001, 0x64, 0, 0, 0, 0], 64⟩] }
  "2a00:1450:4001:64:a:0:100:0" = "deny 2a00:1450:4001:64:a:0:100:0"
-- Prefixes: the strict form, no bits after the length.
#guard parsePrefixString "10.0.0.0/8" = some (.v4 ⟨ip4 10 0 0 0, 8⟩)
#guard parsePrefixString "64:ff9b::/96" = some (.v6 ⟨ip6 [0x64, 0xff9b, 0, 0, 0, 0, 0, 0], 96⟩)
#guard parsePrefixString "::/0" = some (.v6 ⟨ip6 [0, 0, 0, 0, 0, 0, 0, 0], 0⟩)
#guard parsePrefixString "10.0.0.1/8" = none
#guard parsePrefixString "10.0.0.0/08" = none
#guard parsePrefixString "10.0.0.0/33" = none
#guard parsePrefixString "10.0.0.0" = none
#guard parsePrefixString "10.0.0.0/" = none
#guard parsePrefixString "::/129" = none
#guard parsePrefixString "fe80::/10/1" = none
#guard parsePrefixString "[::]/0" = none

end UrlFence.Addr.Examples
