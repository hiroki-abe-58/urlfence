# URLFence

A URL host allowlist check for AI-agent web tools (fetch, browse, documentation lookup): "may this
agent request this URL?", and a check of the addresses a host name resolves to: "may it connect
there?". Both are written and proven in Lean 4, and come with a command-line tool.

```console
$ urlfence check --allow docs.python.org --allow '*.example.com' -- https://docs.python.org/3/ https://docs.python.org.evil.com/ https://docs.python.org@evil.com/
{"input":"https://docs.python.org/3/","decision":"allow","scheme":"https","host":"docs.python.org","port":null}
{"input":"https://docs.python.org.evil.com/","decision":"deny","scheme":"https","host":"docs.python.org.evil.com","port":null}
{"input":"https://docs.python.org@evil.com/","decision":"reject","reason":"userinfo"}
```

Status: v0.1.0, experimental.

> **URLFence decides on the URL string, and it fails closed.** It accepts only a strict, canonical
> form of `http(s)` URLs and refuses everything else, including many URLs a browser would accept.
> `urlfence check` does not resolve DNS, so a name it allows can still point to an internal address
> (DNS rebinding): check each resolved address with `urlfence addr` and connect only to a checked
> one, as [`examples/guarded_fetch.py`](examples/guarded_fetch.py) and, for Node,
> [`examples/guarded_fetch.mjs`](examples/guarded_fetch.mjs) do. It does not follow redirects
> either: check every hop, not only the first URL. See
> [What it does not cover](#what-it-does-not-cover).

## Why

Checks on URLs keep failing in the same few ways, including in AI-agent tools:

* **A string prefix or suffix instead of a hostname comparison:**
  * [CVE-2026-24052](https://www.cve.org/CVERecord?id=CVE-2026-24052), Claude Code WebFetch before
    1.0.111: `startsWith`, so `modelcontextprotocol.io.example.com` passed;
  * [CVE-2026-46341](https://www.cve.org/CVERecord?id=CVE-2026-46341), Apify MCP server before
    0.9.21: `startsWith`, so `docs.apify.com.evil.com` passed, and so did `docs.apify.com@evil.com`;
  * [CVE-2026-33393](https://www.cve.org/CVERecord?id=CVE-2026-33393), Discourse: `end_with?` with
    no dot boundary, so `attacker-example.com` passed.
* **Userinfo taken for the host:** [CVE-2025-47241](https://www.cve.org/CVERecord?id=CVE-2025-47241),
  browser-use before 0.1.45.
* **Normalising before checking:** [CVE-2026-6322](https://www.cve.org/CVERecord?id=CVE-2026-6322),
  fast-uri before 3.1.2, decoded a percent-encoded `@` in the host.
* **IP literals in unexpected forms:** [CVE-2026-49857](https://www.cve.org/CVERecord?id=CVE-2026-49857),
  auth-fetch-mcp before 3.0.2: its private-address blocklist missed an IPv4-mapped IPv6 loopback
  address.
* **Internal addresses written in IPv6:**
  * [CVE-2026-42449](https://www.cve.org/CVERecord?id=CVE-2026-42449), n8n-mcp 2.47.4 to 2.47.13:
    a URL validator with no IPv6 checks let IPv4-mapped addresses such as
    `[::ffff:169.254.169.254]` through;
  * [CVE-2026-44430](https://www.cve.org/CVERecord?id=CVE-2026-44430), MCP Registry before 1.7.7:
    its blocklist covered no 6to4, NAT64 (`64:ff9b::/96`, `64:ff9b:1::/48`) or site-local
    (`fec0::/10`) addresses;
  * [GHSA-cg7w-rg45-pc59](https://github.com/advisories/GHSA-cg7w-rg45-pc59) (CVE-2026-48782),
    pydantic-ai before 1.102.0 (before 2.0.0b3 on the 2.0 line): an earlier fix decoded
    IPv4-mapped, 6to4 and `64:ff9b::/96` addresses, but not IPv4-compatible ones, `64:ff9b:1::/48`,
    other NAT64 prefixes or ISATAP.

The advisories' common lesson is to parse first, then compare hostnames exactly or by a dot-bounded
suffix, and to decide on the address, in every form that carries one. URLFence does that, with
theorems about what it decides. [`UrlFence/Examples.lean`](UrlFence/Examples.lean) and
[`UrlFence/Addr/Examples.lean`](UrlFence/Addr/Examples.lean) run inputs in the style of these bugs
at build time. (They do not reproduce the original programs.)

## The rules

A URL is accepted only in this form, and refused with a reason otherwise:

1. Every character is printable ASCII other than space and backslash (`chars`).
   * Browsers strip tabs and newlines, and read `\` as `/`.
   * Non-ASCII hosts (IDNA) are not supported, and neither are IDNA A-labels (`xn--…`), which
     WHATWG parsers decode and may reject.
2. It starts with `http://` or `https://`, in lowercase (`scheme`). `https:/x`, `https:x`, `HTTPS://x`
   and other forms a browser accepts are refused.
3. The authority (up to the first `/`, `?` or `#`) has no `@` (`userinfo`), no `%` (`percent`), and
   no `[` or `]` (`ipv6`: IPv6 literals are not supported).
4. The authority is a host, optionally followed by `:` and a port. The port is 1 to 65535, written
   without leading zeros (`port`). Port 0 is refused, since some clients silently replace it with the
   default port.
5. The host (`host`) is one of:
   * **a domain:** lowercase labels of `a-z`, `0-9` and `-`, 1 to 63 characters each, not starting
     or ending with `-`, at most 253 characters in all, with no trailing dot. The last label must not
     look like a number: all digits, or `0x` followed by hex digits. Browsers read such hosts as
     IPv4 addresses;
   * **an IPv4 address:** four decimal parts `0` to `255`, without leading zeros. `127.1`,
     `0x7f.0.0.1`, `017.0.0.1` (octal to a browser) and `2130706433` are refused.

The path, query and fragment are kept as written; they never affect the decision.

**Patterns** name a host exactly (`docs.python.org`, `192.0.2.1`), or every strict subdomain of a
domain (`*.example.com`). A subdomain pattern matches `a.example.com` and `a.b.example.com`. It does
not match `example.com` (add that pattern too), `attacker-example.com` or `example.com.evil.net`. A
URL is **allowed** when it is accepted, its scheme is allowed (`https` only, unless `--scheme` says
otherwise), its host matches an allowed pattern, and it matches no denied pattern.

## Resolved addresses

An allowed name can resolve to an internal address. `urlfence addr` checks resolved addresses
against the IANA [IPv4](https://www.iana.org/assignments/iana-ipv4-special-registry/) and
[IPv6](https://www.iana.org/assignments/iana-ipv6-special-registry/) Special-Purpose Address
Registries, as last updated on 2025-10-09 (the CSV files are kept in [`data/`](data), with their
source and the steps to update them):

```console
$ urlfence addr -- 8.8.8.8 ::ffff:127.0.0.1 2002:a9fe:a9fe::1 fe80::1%eth0
{"input":"8.8.8.8","decision":"allow","family":"ipv4","addr":"8.8.8.8"}
{"input":"::ffff:127.0.0.1","decision":"deny","family":"ipv6","addr":"::ffff:7f00:1","reason":"mapped 127.0.0.1: registry 127.0.0.0/8 Loopback"}
{"input":"2002:a9fe:a9fe::1","decision":"deny","family":"ipv6","addr":"2002:a9fe:a9fe::1","reason":"registry 2002::/16 6to4"}
{"input":"fe80::1%eth0","decision":"reject","reason":"parse"}
$ urlfence addr --nat64 64:ff9b::/96 -- 64:ff9b::808:808 64:ff9b::a9fe:a9fe
{"input":"64:ff9b::808:808","decision":"allow","family":"ipv6","addr":"64:ff9b::808:808"}
{"input":"64:ff9b::a9fe:a9fe","decision":"deny","family":"ipv6","addr":"64:ff9b::a9fe:a9fe","reason":"nat64-embedded 169.254.169.254: registry 169.254.0.0/16 Link Local"}
```

**Text forms.** An IPv4 address is four decimal parts `0` to `255` without leading zeros, as in a
URL host. An IPv6 address is in one of the forms of RFC 4291, section 2.2: eight groups of 1 to 4
hex digits in either case, at most one `::`, and possibly a dotted quad for the last 32 bits. Zone
IDs (`%eth0`), brackets, prefix lengths and spaces are refused (`reject`, reason `parse`). The
address is printed in the form of RFC 5952 (lowercase, no leading zeros, `::` for the first longest
run of two or more zero groups), without its section 5 mixed form: `::ffff:127.0.0.1` prints as
`::ffff:7f00:1`.

**The policy.**

* An IPv4 address is denied if it is in a registry row whose "Globally Reachable" value is not
  `True` (`False`, `N/A`, or empty for a terminated allocation), in 224.0.0.0/4 (multicast, which
  is not in the registry), or in a `--deny` prefix.
* An IPv4-mapped address (`::ffff:0:0/96`) gets the decision of the IPv4 address it carries, and so
  does an address in a NAT64 prefix given with `--nat64`.
* Any other IPv6 address is allowed only inside 2000::/3, outside every registry row that is not
  globally reachable and every `--deny` prefix, and only if, when its interface identifier is an
  ISATAP one (`0000:5efe` with any u and g bits), the IPv4 address in it is allowed. So everything
  outside 2000::/3 is denied: `::/96` (IPv4-compatible), `64:ff9b:1::/48`, `100::/64`, `5f00::/16`,
  `fc00::/7`, `fe80::/10`, `fec0::/10`, `ff00::/8` and the rest.
* A `--deny` prefix applies to every address of its family, including the IPv4 address inside an
  IPv6 one. A prefix is `ADDRESS/LENGTH` with a length of at most 32 or 128, written without
  leading zeros, and no address bits set after it; anything else is a usage error.
* The `reason` of a denial names the first rule that denies it: `registry <block> <name>`,
  `multicast 224.0.0.0/4`, `outside 2000::/3`, `deny <prefix>`, or `mapped <ipv4>: …`,
  `nat64-embedded <ipv4>: …` and `isatap <ipv4>: …` followed by the reason for that IPv4 address.

**Deliberately stricter than the registries.** A row that is not globally reachable denies all of
its block, even where a more specific row says `True`:

* all of 192.0.0.0/24, including 192.0.0.9 (PCP anycast) and 192.0.0.10 (TURN anycast);
* all of 2001::/23, including Teredo (2001::/32, `N/A`) and the rows marked `True`: 2001:1::1 to
  2001:1::3 (PCP, TURN and DNS-SD SRP anycast), 2001:3::/32 (AMT), 2001:4:112::/48 (AS112),
  2001:20::/28 (ORCHIDv2) and 2001:30::/28 (DETs);
* all of 6to4 (2002::/16, `N/A`), whatever IPv4 address it carries, and the terminated rows
  192.88.99.0/24 and 2001:10::/28;
* `64:ff9b::/96` (`True`) unless it is given with `--nat64`; then the IPv4 address inside decides.

The anycast addresses are answered by the local gateway or border routers, and 6to4 and Teredo
depend on relays the caller does not control: none of them is a destination an agent's request
should reach.

**NAT64.** `--nat64` takes a /96 (no bits set after it) that URLFence honours: `64:ff9b::/96`, or a
/96 inside 2000::/3 that has no address in common with a registry row that is not globally
reachable. Anything else, such as the RFC 8215 local-use prefix `64:ff9b:1::/96`, a ULA or a
documentation prefix, is a usage error (exit status 2) rather than a prefix that would be silently
ignored. Configuring NAT64 prefixes allows nothing beyond `64:ff9b::/96` with an allowed IPv4 address
inside, or what is allowed without them (`allows_nat64_wellKnown`). In the library, a configured
prefix that is not honoured is ignored, and with the current tables all its addresses are denied
(or, in `::ffff:0:0/96`, decided as IPv4-mapped); that holds for these tables but is not a theorem.

**What is not decoded.** Only IPv4-mapped addresses, the configured /96 NAT64 prefixes and ISATAP
identifiers are decoded; 6to4 and Teredo are denied. An address inside 2000::/3 that carries an
IPv4 address in another way is decided as a plain global address: a network-specific NAT64 prefix
that is not configured (`2a00:1450:64::a00:1`, carrying 10.0.0.1, is allowed; RFC 6052 forbids
non-global IPv4 addresses only in the well-known prefix), the RFC 6052 prefix lengths 32 to 64,
6rd, MAP-E and MAP-T, and SIIT-EAM. A network that uses them must deny their prefixes with
`--deny`.

**What the registries do not know.** Internal services on global addresses are allowed unless you
deny them: a cloud provider's host endpoints (Azure's 168.63.129.16, for example) and your own
public IPv4 and IPv6 ranges. The tables are a snapshot: a block that IANA later adds as not globally
reachable is allowed until they are updated ([`data/README.md`](data/README.md)).

**Together with the URL check.** Check the URL with `urlfence check`, resolve its host, check every
address with `urlfence addr`, refuse if any is denied, and connect to a checked address without
resolving the name again, keeping the URL's host for the `Host` header and the TLS server name. Do
it again on every redirect. [`examples/guarded_fetch.py`](examples/guarded_fetch.py) and
[`examples/guarded_fetch.mjs`](examples/guarded_fetch.mjs) do this by default (see [Usage](#usage)).

## What is proven

The theorems are in [`UrlFence/`](UrlFence), checked by Lean v4.35.0, with no `sorry` and only
Lean's standard axioms. [`scripts/audit.sh`](scripts/audit.sh) checks this, for every declaration in
the library's modules (helper and generated lemmas included), and pins the published theorems
below; see [How it is checked](#how-it-is-checked).

| Theorem | Statement |
| --- | --- |
| `parse_authority`, `isDelim_iff` | In an accepted URL, the authority (from `//` up to the first `/`, `?`, `#` or the end; exactly those three characters) is the host followed by the optional `:port`, and the rest starts with one of those characters. |
| `parseHost_chars` | The host consists of `a-z`, `0-9`, `-` and `.` only, so it contains none of `/ ? # : @ [ ]`. With `parse_authority`, the host is the text between `//` and the first `:`, `/`, `?`, `#` or the end. |
| `parse_render` | An accepted string is exactly the printed form of its parse: nothing is normalised. |
| `parse_no_userinfo` | In an accepted URL, nothing between `//` and the first `/`, `?` or `#` is an `@`. |
| `parse_valid`, `parseHost_valid`, `parseHost_render` | The host of an accepted URL is in one of the accepted forms, and prints back to exactly its text. |
| `parseScheme_spec`, `splitPort_spec` | The scheme prefix and the port are split off exactly as written. |
| `check_allow_iff` | `check` allows a URL **iff** it parses, its scheme is allowed, its host matches an allowed pattern, and it matches no denied pattern. |
| `check_allow_of_add_deny` | Adding a denied pattern never allows more. |
| `exact_matches_iff` | An exact pattern matches exactly its own host. |
| `sub_matches_iff` | `*.d` matches a domain **iff** `d` is not empty and the domain is `d` with at least one label in front. |
| `sub_matches_iff_render` | On printed domains, `*.d` matches **iff** the host ends with `.` followed by `d`. This is the dot boundary whose absence caused the suffix bugs above. |
| `sub_not_ipv4` | A subdomain pattern never matches an IPv4 address. |
| `parsePattern_sub_valid` | A parsed subdomain pattern is a valid domain. |
| `domainOk_noDot`, `join_split`, `split_join`, `split_append_sep`, `join_append` | Splitting at `.` and joining are inverse, and distribute as expected. |

For resolved addresses ([`UrlFence/Addr/`](UrlFence/Addr), namespace `UrlFence.Addr`):

| Theorem | Statement |
| --- | --- |
| `check_allow_iff`, `allows4_iff`, `allows6_iff`, `embeds_iff`, `nat64Ok_iff` | `check` allows an address **iff** its text parses to it and the policy above allows it, stated rule by rule. |
| `registry4_denied`, `registry6_denied`, `multicast4_denied`, `outside_global_denied` | Every address in a registry row that is not globally reachable is denied (for IPv6, except in `::ffff:0:0/96`, which is decided as IPv4-mapped), and so is every IPv4 multicast address, and every IPv6 address outside 2000::/3 that carries no IPv4 address. |
| `mapped_denied`, `mapped_allows_iff`, `nat64_denied`, `nat64_allows_iff`, `isatap_denied` | The IPv4-mapped, NAT64 (in any configured prefix) and ISATAP (any prefix, any u and g bits) addresses of a denied IPv4 address are denied; a mapped or honoured NAT64 address is allowed **iff** its IPv4 address is and no denied IPv6 prefix contains it. |
| `sixToFour_denied`, `teredo_denied` | Every 6to4 and every Teredo address is denied. |
| `allows_nat64_wellKnown` | Configuring NAT64 prefixes allows nothing beyond `64:ff9b::/96` with an allowed IPv4 address inside, or what is allowed without them. |
| `allows_of_add_deny4`, `allows_of_add_deny6` | Denying another prefix never allows more. |
| `explain_eq_none_iff` | A denial reason exists **iff** the address is denied. |
| `parse_render`, `render6_canonical`, `hex16_canonical` | A printed address parses back to itself, and the IPv6 form is that of RFC 5952, section 4. |
| `parse4_eq_some_iff`, `parse4_isSome_iff` | An IPv4 text is read as `v` **iff** it is the printed form of `v`, and is accepted **iff** the URL host parser reads it as an IPv4 address. |
| `Prefix.contains_iff_getMsbD`, `Prefix.contains_iff`, `contains_iff_range4`, `contains_iff_range6`, `ipv4Registry_blocks`, `ipv6Registry_blocks` | Prefix membership is equality of the first bits; every registry block is a CIDR block, so membership is a range of addresses. The audit pins of the last two cover the registry tables. |
| `parsePrefix_v4`, `parsePrefix_v6` | A parsed `--deny` or `--nat64` prefix is a CIDR block. |

### Where the proofs end

The theorems say what URLFence's own parser and matcher do, and pin the reading of an accepted URL
(the host is exactly the text between `//` and the first `:`, `/`, `?`, `#`). **That a WHATWG URL
parser (what browsers and Node use) reads every accepted URL the same way is tested, not proven.**

For addresses, **that the Lean tables are the IANA registries is checked by a script, not proven**
([`scripts/check_registry.py`](scripts/check_registry.py) compares them with the CSV files), and
**that URLFence reads IPv6 text as `inet_pton` does is tested, not proven** (for IPv4 the reading is
proven: `parse4_eq_some_iff`). What the network does with an allowed address, a NAT64 gateway
included, is outside the model.

The CLI ([`Main.lean`](Main.lean)) calls the library directly. Its argument parsing, stdin decoding
and JSON output are ordinary code, covered by tests.

## How it is checked

* `lake build` checks the proofs and runs the `#guard` examples.
* `scripts/audit.sh`:
  * before running Lake, checks `lakefile.lean`, `lean-toolchain` and `lake-manifest.json` against
    pinned SHA-256 hashes (a lakefile is code Lake runs), so any build-configuration change must
    change the audit too, visibly;
  * rejects `sorry`, `native_decide`, axioms, `implemented_by`/`extern`, `partial`/`unsafe`, `#eval`,
    `#exit`, kernel-skipping options and metaprogramming commands in the library source;
  * checks the compiled environment:
    * the library imports only `Init` and its own modules;
    * no compiled code is replaced;
    * every declaration depends on no axiom beyond the standard three;
    * the published theorems are pinned in
      [`scripts/statements.expected`](scripts/statements.expected), both as printed text and as a
      SHA-256 hash of the raw terms of every UrlFence definition they depend on (constructors
      included). A renamed theorem, a weakened statement or a changed definition behind it fails;
  * replays every module through `leanchecker`.

  CI checks the pins before anything builds. The audit does not protect its own inputs (this
  script, `scripts/Axioms.lean`, `scripts/statements.expected`, the CI workflow): a change to them
  shows in the diff, but whoever can change them can change the audit.
* `tests/test_cases.py` runs fixed cases in the style of the advisories, and checks the CLI's
  contract.
* `tests/test_whatwg.py` compares URLFence with Node's WHATWG `URL` on about 10,000 random and
  adversarial URLs, including printable ASCII characters inserted into hosts at random positions.
  For every URL URLFence accepts, WHATWG must read:
  * the same scheme, host and port (`:443` and `:80` count as the default);
  * no userinfo;
  * a host for which the matching rules give the same decision.

  URLFence may refuse what WHATWG accepts, and on these inputs it refuses about 6,000 such URLs.
  Skipped if `node` is not installed.
* `tests/compat.py` checks that common HTTP clients read every accepted URL as URLFence does, on a
  deterministic corpus of 41,647 URLs, 17,044 of them accepted (its size and SHA-256 are pinned in
  the script). There are three views, reported separately:
  * parser: Node's WHATWG `URL`, Python's `urllib.parse.urlsplit` and `urllib.request.Request`,
    `urllib3.util.parse_url`, `requests` (its URL preparation, then urllib3) and curl
    (`--write-out '%{url.*}'`), with no network;
  * request: what `urllib.request`, `urllib3`, `requests` and curl actually ask for, seen by an HTTP
    proxy fixture on 127.0.0.1 that answers 403. For http that is the absolute URL, the `Host`
    header and any `Authorization` header; for https it is only `CONNECT host:port`, so userinfo,
    the TLS server name and the inner `Host` header are not seen. curl is always given the
    fixture as its proxy, and while the Python clients run, any address lookup other than for the
    fixture's address and port is refused and fails the run, so nothing leaves the machine. This
    is the proxy path only, and there is no proxy view for Node;
  * direct: what Node's `http.request`/`https.request` (`node`), `urllib.request`, `urllib3`,
    `requests` and curl do with no proxy. Each connection the client opens is sent to a fixture on
    127.0.0.1 instead of where the client was going, and that target is recorded: for Node by an
    Agent's `createConnection` ([`tests/compat_direct.js`](tests/compat_direct.js)), for the Python
    clients by answering the one address lookup inside `socket.create_connection` or urllib3's
    `create_connection` with the fixture's address, and for curl by `--connect-to` rules that send
    it to one of four fixture ports depending on whether its own host and port are URLFence's (curl
    matches these rules ignoring ASCII case). The client must connect to URLFence's host and port. For http it must send an origin-form request
    whose `Host` header names them, without an `Authorization` header. For https it must send the
    host as the TLS server name (SNI, read from the ClientHello; for an IPv4 host, none or the
    address), and a Python client must give the host as `server_hostname` (the name it would
    verify the certificate against), when it gives one. The fixture then answers 403 or a fatal TLS
    alert, so the handshake never completes: what an allowed name resolves to (nothing is resolved,
    and how the system resolver reads a name is not tested either: glibc accepts `127.1`, `0x7f.1`
    and octal parts, which URLFence's host rules refuse), whether the certificate is actually
    verified, and everything inside TLS (the inner request and its `Host` header) are not observed.
    Node refuses and reports any lookup or connection other than to the fixture, and the Python
    clients keep the lookup guard above; curl only ever has 127.0.0.1 to connect to. One client
    behaviour seen on the way: urllib3 2.0.7 drops URL userinfo on its direct path but forwards it
    in the request line to an HTTP proxy, so credentials in a URL reach the proxy (URLFence refuses
    userinfo, so accepted URLs carry none).

  A disagreement fails the run. A client that is not installed is reported as skipped, never as
  agreeing. A client that refuses an accepted URL is listed separately; `--strict` fails on it, and
  so does any view that refuses more than 1% of the URLs. `--self-test` checks that every view
  reports a difference for each of 7 deliberately wrong expectations (host and port over http and
  https, userinfo over http), except in 6 listed cases where the client sends nothing that would
  show one, which must then happen exactly as listed: on its direct path `urllib.request` refuses a
  `user:password@` URL and urllib3 drops the userinfo, and requests ignores a userinfo without a
  password. [`tests/test_compat_direct.py`](tests/test_compat_direct.py) checks the ClientHello
  parser and the direct views' comparisons on their own.
  With Python 3.12.3, urllib3 2.0.7, requests 2.31.0, curl 8.5.0 and Node 18.19.1, the full corpus
  gives no disagreement in any view, and one refusal: urllib3, and requests through it, parse a
  path that starts with `//` again as an authority, and refuse `https://b//yc%80a:;` without
  sending anything, through the proxy and directly.
  CI runs the self-test and a fixed 1/16 subset with `--strict`, and requires `whatwg`, `node`,
  `urlsplit`, `urllib.request` and curl; urllib3 and requests run there only if the runner has
  them. Run `python3 tests/compat.py` for the full corpus. These are tests on this corpus and
  these client versions, not proofs.
* [`scripts/check_registry.py`](scripts/check_registry.py) (in CI and `scripts/reproduce.sh`)
  compares the registry tables in [`UrlFence/Addr/Registry.lean`](UrlFence/Addr/Registry.lean) with
  the IANA CSV files, row by row: each block's value and length (read with Python's `ipaddress`),
  the "Globally Reachable" value, the name, and the block as URLFence prints it. It also checks the
  files' SHA-256.
* [`tests/test_addr.py`](tests/test_addr.py) checks `urlfence addr`:
  * its parser against `socket.inet_pton` and `ipaddress` on 50,000 deterministic strings (address
    forms, mutations of them, random strings). Every accepted string must give the same bytes as
    both and print as `ipaddress` prints it; every refused string must be refused by `inet_pton`
    too (`ipaddress` also accepts zone IDs). With Python 3.12.3: 25,889 accepted, 24,111 refused
    (counted by category: zone IDs, brackets, IPv4 not in four parts, leading zeros, …), no
    difference. This needs glibc's `inet_pton` (Linux) and Python 3.9.5 or later;
  * its decisions against `ipaddress.is_global` on 333 addresses: the edges of every registry block,
    of 2000::/3 and of 224.0.0.0/4, and the mapped, IPv4-compatible, NAT64, 6to4, Teredo, ISATAP and
    site-local forms of nine IPv4 addresses. Every difference must match an entry of a list with
    its reason, all of them addresses URLFence denies and `is_global` calls global: the blocks
    denied as a whole above, registry rows the running Python's table does not list (3.12.3 lacks
    3fff::/20, 5f00::/16 and 100:0:0:1::/64; versions before the CVE-2024-4032 update also lack
    2002::/16), multicast, space outside 2000::/3, ISATAP, and mapped addresses of IPv4 addresses
    that are not private but not globally reachable either (100.64.0.0/10). How many there are
    depends on the Python version, whose table changes between releases: 105 with Python 3.12.3
    (Ubuntu), 100 with 3.10.20, 3.12.13 and 3.13.14, 120 with 3.11.9.
    `python3 tests/test_addr.py --table` prints them;
  * the CLI's contract: fields, exit status, reasons, NAT64 and prefix usage errors, stdin
    encoding and ASCII output.
* `tests/test_guarded_fetch.py` runs the example against the real binary. Unpinned, an HTTP proxy on
  127.0.0.1 stands in for the web: a redirect to another host, or to a URL with userinfo, is
  refused before it is requested, and the body is cut at `max_bytes`. Pinned, `getaddrinfo` is
  replaced by a table of answers and the example's `open_socket` by a function that records where
  the fetch connects and sends the connection to an origin fixture on 127.0.0.1 (the answers that
  should succeed are public addresses, so the policy needs no exception for the fixture). Loopback,
  private, metadata, mapped, IPv4-compatible, NAT64, 6to4, Teredo, ISATAP, ULA, link-local and
  site-local answers, alone or mixed with a public one, are refused with no connection; an answer
  that turns from public to loopback is refused on the next hop; the request keeps the URL's host
  in `Host` and, for https, as the TLS server name. Unusable answers from the binary, simulated by
  replacing `subprocess.run`, refuse. A body shorter than its Content-Length refuses, unpinned and
  pinned (also with `max_bytes` None or -1), and pinned over https from an origin that closes without
  close_notify (its throwaway certificate needs openssl). A flood of trailer lines after a chunked
  body, or of `100 Continue` responses before the response, refuses, unpinned and pinned (and
  pinned over https), while a few of either do not, and a refused fetch leaves no file descriptor
  open. Over a connection in memory, where how much was read is exact, a flood (also of chunk
  extensions) is refused within the bounds below, pinned and unpinned (for http and https, so
  through both urllib handlers), a head of exactly 64 KiB passes and one byte more does not, and
  ordinary answers are read byte for byte as http.client reads them. Every test runs with
  `tests/common.py` refusing, before the call, any connection beyond loopback and any lookup of a
  name made through Python's `socket` module, whoever makes it (http.client, urllib and ssl
  included); tests try 192.0.2.1, plain and for TLS, to check it.
* `tests/test_guarded_fetch_node.py` runs the Node example the same way, under node, through
  [`tests/guarded_fetch_node.mjs`](tests/guarded_fetch_node.mjs): there every `net.Socket` connect
  call is recorded with the host and port the example gave it and sent to a fixture on 127.0.0.1
  instead, `dns.lookup` refuses (and must not be called), and the resolver answers from a table
  (in one test, throwing on any lookup beyond one per hop). It covers the pinned cases above, the
  request target, a redirect to another allowed host whose address is denied, an answer whose
  `addr` is not the address checked, the environment proxies, `pin: false`, and the example's
  `openSocket` against a listener (numeric addresses only, with and without `autoSelectFamily`),
  a redirect to raw forms that WHATWG normalises (checked and requested as the normalised string),
  and refused `tls` options and timeouts. With openssl, https fixtures with throwaway self-signed
  certificates check that the certificate must match the URL's host, not the address connected
  to, and is verified, pinned or not, under `NODE_TLS_REJECT_UNAUTHORIZED=0`. Unusable answers come
  from a stand-in binary (`URLFENCE_BIN`). Every name is under `.invalid`, and the driver refuses,
  before net connects, any connection that goes to no fixture (a test tries 192.0.2.1, plain and
  over TLS). Skipped without node or openssl, unless `URLFENCE_REQUIRE` names them, as CI and
  `scripts/reproduce.sh` do.
* `tests/mutants.py` plants 31 plausible bugs, one at a time, and requires each one to be caught.
  They include the CVE-style prefix and suffix mistakes, a wrong authority boundary, accepting
  octal IPv4 parts, and for addresses: no IPv4-mapped decoding, the IPv4 address taken at the wrong
  offset, the 6to4 row dropped, a prefix length off by one, the ISATAP `0200:5efe` form missed,
  multicast allowed, `64:ff9b::/96` treated as global, and the CLI ignoring a NAT64 prefix that
  URLFence would not honour; in the Node example: addresses not checked again after a redirect, a
  connection to the host name instead of the checked address, and an answer's `addr` not compared
  with the address checked; and in the Python example, a body shorter than its Content-Length
  returned as if whole, responses read with no bound, unpinned https responses read with no bound,
  the head not bounded, and the end of the bound read as the end of the stream. So far every one in
  the library fails the build, and the script names the file: a theorem or a build-time example;
  the one in the CLI fails `tests/test_addr.py`, the three in the Node example fail
  `tests/test_guarded_fetch_node.py`, and the five in the Python example fail
  `tests/test_guarded_fetch.py`.
  Some fail only because a proof script no longer fits the changed code, not because a statement
  became false.
  Dropping the userinfo check or the percent check changes only the reason for a rejection, since
  the host grammar refuses those characters anyway. Dropping the backslash check also lets a
  backslash through in the path, query or fragment, with the host unchanged.

[`scripts/reproduce.sh`](scripts/reproduce.sh) runs all of this from a fresh clone of the current
commit in a temporary directory: the pins, the build, the audit, the registry check, the tests, the
client comparison on the full corpus and the mutation check, and prints the binary's SHA-256. It
takes about three minutes, and, like CI, fails if node, curl or openssl is missing.

## Usage

Build with [elan](https://github.com/leanprover/elan) installed:

```sh
lake build
.lake/build/bin/urlfence check --allow docs.python.org --allow '*.github.com' --deny gist.github.com -- "$URL"
```

```
urlfence check --allow PATTERN ... [--deny PATTERN ...] [--scheme http|https ...] [--stdin] [-- URL ...]
urlfence addr [--nat64 PREFIX/96 ...] [--deny PREFIX ...] [--stdin] [-- ADDRESS ...]
```

* URLs go after `--`, or one per line on stdin with `--stdin`. Stdin is read whole before the
  first answer.
* For a given policy, time and memory grow linearly with the input. On an Intel Core Ultra 9 285K (WSL2), 1,000,000
  URLs on stdin (24 MB) took 2.7 s and 600 MiB, and one 16 MB URL 1.5 s and 1.6 GiB: expect
  roughly 25 to 100 times the input size in memory, and split very large batches. These are
  measurements: the theorems say nothing about time or memory. When memory runs out, the process
  is killed by a signal, or, if an allocation fails (under `ulimit -v`, say), it prints `INTERNAL
  PANIC: out of memory` and exits with status 1, possibly after some result lines. Use the output
  only if it has exactly one result line per input and the exit status matches the decisions;
  anything else is a failure, not an answer.
* One ASCII JSON object per URL: `decision` is `allow`, `deny` or `reject`, with `scheme`, `host` and
  `port`, or a `reason`. For `addr`, one per address, with `family` (`ipv4` or `ipv6`) and `addr`
  (the printed form), and a `reason` for `deny` and `reject`.
* Exit status: 0 if at least one URL or address was checked and all are allowed, 1 otherwise, and 2
  for a usage error, including an invalid pattern or prefix, a NAT64 prefix URLFence would not
  honour, or nothing to check.
* **Send the request to exactly the URL you checked.** If you rebuild it, rebuild it from `scheme`,
  `host` and `port`, never from your own parse of the input.
* **Check every redirect.** A client that follows `Location` by itself sends the next request
  unchecked.

[`examples/guarded_fetch.py`](examples/guarded_fetch.py) is an example of all of this in Python, to
adapt, not a hardened client: `guarded_fetch(url, allow=[...])` checks the URL, refuses unless
URLFence's answer is one JSON object for exactly that URL with a matching exit status, requests
(GET) exactly the checked URL, and checks each redirect target before following it. It returns
`(status, body, hops)` for the last response, whatever its status, or raises `Refused` (refused,
or the request failed).

By default (`pin=True`) it also pins the connection: on every hop it resolves the host once, runs
`urlfence addr` on every answer (`deny_addr` and `nat64` are passed as `--deny` and `--nat64`),
refuses before connecting if any answer is denied, and connects to a checked address itself, so the
name is not resolved again; the `Host` header and, for https, the TLS server name and the name the
certificate must match stay the URL's host. A proxy resolves names itself, so with `pin=True` a
`proxies` argument is an error, and a proxy set in the environment for the scheme refuses
(`no_proxy` is honoured). `pin=False` requests the URL through urllib (and any proxy) without
checking addresses; the proxy must then enforce its own address policy. Pinning is the default
because it closes the gap the URL check leaves open, at the cost of not working through a proxy.

It does nothing about the port or the path, or what a proxy or the server does with the request
(see below). It bounds the body (`max_bytes`), the number of redirects, and what http.client reads
of each response: at most 64 KiB (`HEAD_BYTES`) for the status line and headers and any
`100 Continue` responses before them, then at most twice `max_bytes` plus 64 KiB for the body, its
chunk framing and its trailer fields. A response that needs more raises `Refused`, so a body sent
in very small chunks (under 5 bytes) is refused rather than cut at `max_bytes` once enough of it
has come: about a third of `max_bytes`, in chunks of 1 byte. On its own, http.client would read
any number of `100 Continue` responses, trailer lines after a chunked body and chunk extensions,
far past `max_bytes`, each socket operation within `TIMEOUT` (seen with Python 3.10.20, 3.11.9,
3.12.3, 3.12.13 and 3.13.14). With `max_bytes` None or negative, only the head is bounded. This
counts what http.client reads after TLS, not TLS records. `TIMEOUT` bounds each `urlfence` run,
each connection attempt (one per address, until one connects), each TLS handshake and each read or
write on the connection (over TLS, a handshake or a read as a whole), not the whole fetch: there is
no deadline. Nor does it bound the name lookup: `getaddrinfo` takes no timeout, and only the
system resolver's own settings end it. A server that sends a byte at a time, each within
`TIMEOUT`, can hold a response for a `TIMEOUT` per byte that http.client may read under the bounds
above (about 2.2 million with the defaults: months), and without end with `max_bytes` None or
negative. A body that ends before its `Content-Length`, because the connection closed early (over
TLS also without close_notify), raises `Refused` rather than coming back short, in the Node example
too.

[`examples/guarded_fetch.mjs`](examples/guarded_fetch.mjs) is the same example for Node 18 and
later (ESM, no dependencies), with the same rules: `await guardedFetch(url, { allow: [...] })`
gives `{ status, body, hops }` or rejects with `Refused`. Its header lists where it differs from
the Python one. Mainly, a `Location` is resolved as WHATWG resolves it (`new URL(location, url)`),
which normalises it before it is checked: the host is percent-decoded and lowercased
(`DOCS%2Eexample.com` becomes `docs.example.com`), tabs and newlines are removed, backslashes
become slashes, dot segments (also `%2e%2e`) and a default port are dropped, IPv4 number forms are
made canonical (`0x7f.1` becomes `127.0.0.1`), and a space in the path becomes `%20`. The Python
example checks urljoin's result instead, and URLFence refuses these raw forms. This is no way
around the check: the normalised string is what is checked, its addresses included, and exactly
what is requested, and a server could have sent that string in the first place.

Pinned (the default), on every hop it resolves the host once (`dns.promises.lookup`, or
the `resolve` option), runs `urlfence addr` on every answer (`denyAddr`, `nat64`), refuses unless
each answer is allowed and its `addr` is the address checked (compared as numbers), and opens the
connection itself: `net.connect` or `tls.connect` with that address as `host`, for which Node's
`net` skips the lookup, and Happy Eyeballs (`autoSelectFamily`) with it; the example also passes a
`lookup` that refuses. The request then goes over that socket, with no Agent. For https the server
name is the URL's host (none for an IPv4 host) and the certificate is checked against the URL's
host, not the address: the example calls `checkServerIdentity` with it. Certificates are verified
even under `NODE_TLS_REJECT_UNAUTHORIZED=0`. `tls` passes on CA, client certificate, cipher and
version options (`ca`, say) and refuses any other, such as `rejectUnauthorized` or
`checkServerIdentity`, which could turn verification off. With `pin: false` these options and
`rejectUnauthorized: true` go to `https.request`, but there the options of the agent used (the
one passed in, or `https.globalAgent`) override them: an agent made with `rejectUnauthorized:
false`, or with its own `ca`, `servername` or `checkServerIdentity`, decides verification.

Proxies: Node 18's `http` and `https` take no proxy from the environment. Node 24.13.0 (its
source read and its agents tried by hand; not in the tests) gives its two global agents a proxy
from `HTTP_PROXY` and `HTTPS_PROXY` (and `NO_PROXY`) when `NODE_USE_ENV_PROXY=1` or
`--use-env-proxy` is set, and `fetch()` one too; agents that code creates, and requests without an
agent, connect directly. Other versions were not examined. Pinning does not depend on this:
a pinned request never uses an Agent, so no proxy can take it over. But so that a configured proxy
is not bypassed without a word, the example refuses to pin when that support may be on
(`NODE_USE_ENV_PROXY` set to anything but `0`, `--use-env-proxy` in the arguments or
`NODE_OPTIONS`, or a global agent with a proxy configuration) and a proxy is set for the scheme;
it does not read `NO_PROXY`. With `pin: false`, `http(s).request` with the `agent` given (or the
global agent, and any proxy it uses) resolves the name itself, and no address is checked; with
`pin: true`, an `agent` is an error.

Its limits are the Python one's, and: `fetch()` (undici) is neither used nor pinned, so a request
made with it is not covered; code that patches `http` or `net` is not guarded against, beyond the
request having to use the example's socket; `timeout` (10 s by default) bounds each `urlfence` run
and each period with no socket activity, not the whole fetch; and the body is cut at `maxBytes`
without saying whether it was cut, as in Python. Node's HTTP parser refuses trailer fields longer
than `--max-http-header-size` (16 KiB by default), but does not limit the number of interim
responses before the response: with Node 18.19.1, the example read 20,000 `100 Continue` responses
(500 kB), then the response.

From Lean, build a policy with `UrlFence.Policy.make` and call `Policy.checkString`; for addresses,
build a `UrlFence.Addr.Config` and call `Config.checkString`.

## What it does not cover

* **DNS.** `urlfence check` decides on the name only. An allowed name can resolve to a private or
  loopback address, or change between the check and the connection (rebinding): check every
  resolved address with `urlfence addr` and pin the connection to a checked one, as the examples
  do. An unpinned connection (one that resolves the name again, or goes through a proxy) is not
  covered: a client that resolves the name itself, such as a browser, curl, requests or urllib, or
  any client with Happy Eyeballs, connects to whatever its own lookup returns, not to an address
  you checked, unless you hand it that address.
* **Addresses the registries cannot tell apart.** `urlfence addr` knows the IANA special-purpose
  blocks, not your network: internal services on global addresses (a cloud provider's host
  endpoints, your own public ranges) are allowed unless you `--deny` them, and so are IPv4
  addresses embedded in ways it does not decode (network-specific NAT64 prefixes you did not
  configure, the RFC 6052 lengths other than /96, 6rd, MAP-E/T, SIIT-EAM). What a NAT64 gateway or
  a proxy then does with an address is outside its view. The registry tables need re-transcription
  when IANA updates them.
* **Other protocols.** The address check is for TCP connections made by the caller; UDP and QUIC
  are not pinned by the examples, and neither are ports.
* **Redirects.** A request to an allowed URL can be redirected anywhere. Re-check every hop, or
  turn redirects off.
* **What the server does.** Open redirects and proxies on an allowed host are out of scope.
* **IPv6 literals and non-ASCII (IDNA) hosts** are refused in URLs, not supported (`urlfence addr`
  takes IPv6 addresses, without brackets).
* **Browser leniency.** Many URLs a browser accepts are refused here: uppercase letters, `https:/x`,
  a trailing dot, short IPv4 forms. Normalise them yourself only if you then check the normalised
  string.
* **Ports and paths.** They are reported, but patterns do not restrict them.
* **Passing the URL on.** Hand the URL to the client as a single argument, never through a shell. The
  path may contain shell metacharacters and curl glob characters (`[`, `{`), so use `curl -g`.
* **CLI input.** A stdin line ending in `\r` (CRLF) is refused as `chars` (as `parse` by `addr`). An
  argument that is not valid UTF-8 is decoded lossily: it reaches the program with U+FFFD and is
  refused as `chars` (as `parse` by `addr`); only stdin reports the bytes (`input_hex`, reason
  `encoding`).

## Related work

* The [WHATWG URL Standard](https://url.spec.whatwg.org/), and Node's implementation of it, used
  here as the test oracle.
* [ammkrn/lean-url](https://github.com/ammkrn/lean-url): a WHATWG URL implementation in Lean 4,
  not verified.
* [PathFence](https://github.com/hiroki-abe-58/pathfence): the same approach for file paths.

## Licence

Copyright 2026 the URLFence authors. Apache-2.0; see [LICENSE](LICENSE).

The code and proofs were written with Claude Code (Claude Opus 5.5). So far they have been reviewed
only by AI, in separate Claude sessions; no human has reviewed them yet.
