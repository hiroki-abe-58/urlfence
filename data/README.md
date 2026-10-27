# IANA special-purpose address registries

The two CSV files here are the CSV exports of the IANA special-purpose address registries,
byte for byte as served (with CRLF line endings; `.gitattributes` keeps git from converting them):

| File | Source | Registry last updated | SHA-256 |
| --- | --- | --- | --- |
| `iana-ipv4-special-registry.csv` | <https://www.iana.org/assignments/iana-ipv4-special-registry/iana-ipv4-special-registry-1.csv> | 2025-10-09 | `cbc4b7653c8bc640ba1e8e5d4ebbf11e7c7a1d867e7f1593aad001d3f8632aac` |
| `iana-ipv6-special-registry.csv` | <https://www.iana.org/assignments/iana-ipv6-special-registry/iana-ipv6-special-registry-1.csv> | 2025-10-09 | `bf56772aef97fbf9b4a27c98b8511f2bb1ba96da4b9ccc12ab203a2496faba66` |

Retrieved with curl on 2026-10-27 at 22:45 UTC, and again at 23:11 UTC with identical contents
(HTTP `Last-Modified`: 2026-10-13 20:07:19 UTC and 20:07:01 UTC). The "last updated" dates are those
of the registries' XML files
(<https://www.iana.org/assignments/iana-ipv4-special-registry/iana-ipv4-special-registry.xml>,
<https://www.iana.org/assignments/iana-ipv6-special-registry/iana-ipv6-special-registry.xml>).

`UrlFence/Addr/Registry.lean` transcribes the address block, name and "Globally Reachable" value of
every row. `python3 scripts/check_registry.py` compares the Lean tables with these files.

## Footnotes

The CSV files carry only the footnote marks (`False [1]`, `192.0.0.0/24 [2]`, ...). The footnotes,
from the XML files:

IPv4 registry:

1. (127.0.0.0/8) Several protocols have been granted exceptions to this rule. For examples, see
   RFC 8029 and RFC 5884.
2. (192.0.0.0/24) Not useable unless by virtue of a more specific reservation.

IPv6 registry:

1. (2001::/23) Unless allowed by a more specific allocation.
2. (2001::/32, Globally Reachable) See RFC 4380, Section 5 for details.
3. (2002::/16) See RFC 3056 for details.
4. (fc00::/7, Globally Reachable) See RFC 4193 for more details on the routability of Unique-Local
   addresses. The Unique-Local prefix is drawn from the IPv6 Global Unicast Address range, but is
   specified as not globally routed.

URLFence denies all of a block that is not globally reachable, including where a more specific row
says `True` (IPv4 footnote 2, IPv6 footnote 1): this is stricter than the registries.
