# URLFence

A URL host allowlist check for AI-agent web tools (fetch, browse, documentation lookup): "may this
agent request this URL?". It is written and proven in Lean 4, and comes with a command-line tool.

```console
$ urlfence check --allow docs.python.org --allow '*.example.com' -- https://docs.python.org/3/ https://docs.python.org.evil.com/ https://docs.python.org@evil.com/
{"input":"https://docs.python.org/3/","decision":"allow","scheme":"https","host":"docs.python.org","port":null}
{"input":"https://docs.python.org.evil.com/","decision":"deny","scheme":"https","host":"docs.python.org.evil.com","port":null}
{"input":"https://docs.python.org@evil.com/","decision":"reject","reason":"userinfo"}
```

Status: v0.1.0, experimental.

> **URLFence decides on the URL string, and it fails closed.** It accepts only a strict, canonical
> form of `http(s)` URLs and refuses everything else, including many URLs a browser would accept.
> It does not resolve DNS, so a name it allows can still point to an internal address (DNS
> rebinding). It does not follow redirects either: check every hop, not only the first URL. See
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

The advisories' common lesson is to parse first, then compare hostnames exactly or by a dot-bounded
suffix. URLFence does that, with theorems about what it decides.
[`UrlFence/Examples.lean`](UrlFence/Examples.lean) runs inputs in the style of these bugs at build
time. (It does not reproduce the original programs.)

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

### Where the proofs end

The theorems say what URLFence's own parser and matcher do, and pin the reading of an accepted URL
(the host is exactly the text between `//` and the first `:`, `/`, `?`, `#`). **That a WHATWG URL
parser (what browsers and Node use) reads every accepted URL the same way is tested, not proven.**

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
  the script). There are two views, reported separately:
  * parser: Node's WHATWG `URL`, Python's `urllib.parse.urlsplit` and `urllib.request.Request`,
    `urllib3.util.parse_url`, `requests` (its URL preparation, then urllib3) and curl
    (`--write-out '%{url.*}'`), with no network;
  * request: what `urllib.request`, `urllib3`, `requests` and curl actually ask for, seen by an HTTP
    proxy fixture on 127.0.0.1 that answers 403. For http that is the absolute URL, the `Host`
    header and any `Authorization` header; for https it is only `CONNECT host:port`, so userinfo,
    the TLS server name and the inner `Host` header are not seen. curl is always given the
    fixture as its proxy, and while the Python clients run, any address lookup other than for the
    fixture's address and port is refused and fails the run, so nothing leaves the machine. This
    is the proxy path only: a client's direct path is not observed, and there is no Node request
    view.

  A disagreement fails the run. A client that is not installed is reported as skipped, never as
  agreeing. A client that refuses an accepted URL is listed separately; `--strict` fails on it, and
  so does any view that refuses more than 1% of the URLs. `--self-test` checks that every view
  reports a difference for each of 6 deliberately wrong expectations (host and port over http and
  https, userinfo over http).
  With Python 3.12.3, urllib3 2.0.7, requests 2.31.0, curl 8.5.0 and Node 18.19.1, the full corpus
  gives no disagreement and one refusal: urllib3, and requests through it, parse a path that starts
  with `//` again as an authority, and refuse `https://b//yc%80a:;` without sending anything.
  CI runs the self-test and a fixed 1/16 subset with `--strict`, and requires `whatwg`, `urlsplit`,
  `urllib.request` and curl; urllib3 and requests run there only if the runner has them. Run
  `python3 tests/compat.py` for the full corpus. These are tests on this corpus and these client
  versions, not proofs.
* `tests/test_guarded_fetch.py` runs the example against the real binary and an HTTP proxy on
  127.0.0.1 that stands in for the web: a redirect to another host, or to a URL with userinfo, is
  refused before it is requested. Unusable answers from the binary, simulated by replacing
  `subprocess.run`, refuse.
* `tests/mutants.py` plants 15 plausible bugs, one at a time, and requires each one to be caught.
  They include the CVE-style prefix and suffix mistakes, a wrong authority boundary, and accepting
  octal IPv4 parts. So far every one fails the build, and the script names the file: a theorem or a
  build-time example. Some fail only because a proof script no longer fits the changed code, not
  because a statement became false. Dropping the userinfo check or the percent check changes only
  the reason for a rejection, since the host grammar refuses those characters anyway. Dropping the
  backslash check also lets a backslash through in the path, query or fragment, with the host
  unchanged.

[`scripts/reproduce.sh`](scripts/reproduce.sh) runs all of this from a fresh clone of the current
commit in a temporary directory: the pins, the build, the audit, the tests, the client comparison
on the full corpus and the mutation check, and prints the binary's SHA-256. It takes about a minute
and, like CI, fails if node or curl is missing.

## Usage

Build with [elan](https://github.com/leanprover/elan) installed:

```sh
lake build
.lake/build/bin/urlfence check --allow docs.python.org --allow '*.github.com' --deny gist.github.com -- "$URL"
```

```
urlfence check --allow PATTERN ... [--deny PATTERN ...] [--scheme http|https ...] [--stdin] [-- URL ...]
```

* URLs go after `--`, or one per line on stdin with `--stdin`.
* One ASCII JSON object per URL: `decision` is `allow`, `deny` or `reject`, with `scheme`, `host` and
  `port`, or a `reason`.
* Exit status: 0 if at least one URL was checked and all are allowed, 1 otherwise, and 2 for a usage
  error, including an invalid pattern or no URLs.
* **Send the request to exactly the URL you checked.** If you rebuild it, rebuild it from `scheme`,
  `host` and `port`, never from your own parse of the input.
* **Check every redirect.** A client that follows `Location` by itself sends the next request
  unchecked.

[`examples/guarded_fetch.py`](examples/guarded_fetch.py) is an example of all of this in Python, to
adapt, not a hardened client: `guarded_fetch(url, allow=[...])` checks the URL, refuses unless
URLFence's answer is one JSON object for exactly that URL with a matching exit status, requests
(GET) exactly the checked string, and checks each redirect target before following it. It returns
`(status, body, hops)` for the last response, whatever its status, or raises `Refused` (refused,
or the request failed). It does nothing about DNS, the port or the path, or what a proxy or the
server does with the URL (see below).

From Lean, build a policy with `UrlFence.Policy.make` and call `Policy.checkString`.

## What it does not cover

* **DNS.** An allowed name can resolve to a private or loopback address, or change between the
  check and the connection (rebinding). Pin the resolved address, or check it, at connect time.
* **Redirects.** A request to an allowed URL can be redirected anywhere. Re-check every hop, or
  turn redirects off.
* **What the server does.** Open redirects and proxies on an allowed host are out of scope.
* **IPv6 literals and non-ASCII (IDNA) hosts** are refused, not supported.
* **Browser leniency.** Many URLs a browser accepts are refused here: uppercase letters, `https:/x`,
  a trailing dot, short IPv4 forms. Normalise them yourself only if you then check the normalised
  string.
* **Ports and paths.** They are reported, but patterns do not restrict them.
* **Passing the URL on.** Hand the URL to the client as a single argument, never through a shell. The
  path may contain shell metacharacters and curl glob characters (`[`, `{`), so use `curl -g`.
* **CLI input.** A stdin line ending in `\r` (CRLF) is refused as `chars`. An argument that is not
  valid UTF-8 reaches the program with U+FFFD and is refused as `chars`; only stdin reports the bytes
  (`input_hex`).

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
