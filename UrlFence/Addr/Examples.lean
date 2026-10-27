import UrlFence.Addr.Check

/-!
# Address examples, checked at build time

The first groups follow published bugs in checks of resolved addresses, where an IPv4 address
written in IPv6 got past a check of the IPv4 forms:

* CVE-2026-49857 (auth-fetch-mcp before 3.0.2): IPv4-mapped loopback `::ffff:7f00:1`;
* CVE-2026-42449: IPv4-mapped metadata address `[::ffff:169.254.169.254]`;
* CVE-2026-44430: 6to4 (`2002::/16`), NAT64 (`64:ff9b::/96`, `64:ff9b:1::/48`) and site-local
  (`fec0::/10`) addresses were not denied;
* CVE-2026-48782 (pydantic-ai): IPv4-compatible `::a.b.c.d`, `64:ff9b:1::/48` and ISATAP.

They show what `Config.check` decides for those inputs. They do not reproduce the original
programs. The cloud metadata addresses follow: 169.254.169.254, 100.100.100.200, 192.0.0.192 and
fd00:ec2::254.
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

end UrlFence.Addr.Examples
