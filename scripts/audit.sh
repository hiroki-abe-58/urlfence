#!/usr/bin/env bash
# Proof audit: no escape hatches in the library, a pinned build configuration, only Lean's standard
# axioms behind any of its declarations, no other code reaching it, compiled code that is the proven
# code, the published theorem statements and the definitions they depend on unchanged, and every
# module accepted by the kernel's own checker.
#
# What this does not check: that Main.lean (the CLI) calls the library as documented. That is
# ordinary code, covered by review and by the tests. Nor does it protect its own inputs (this file,
# scripts/Axioms.lean, scripts/statements.expected, the CI workflow): it makes changes visible in a
# diff; it is not a gate against whoever can change those files.
#
#   scripts/audit.sh                     run the audit
#   scripts/audit.sh --pins              only check the pinned build configuration (needs no Lake;
#                                        CI runs it before anything builds)
#   scripts/audit.sh --print-statements  print the published statements and their SHA-256 pins (to
#                                        review a change to scripts/statements.expected)
set -euo pipefail
cd "$(dirname "$0")/.."

fail() { echo "audit: $*" >&2; exit 1; }

PUBLISHED="join_split split_join split_append_sep join_append parseHost_render parseHost_valid parseHost_chars
  domainOk_noDot parseScheme_spec splitPort_spec parse_render parse_valid parse_no_userinfo parse_authority
  isDelim_iff sub_not_ipv4 exact_matches_iff sub_matches_iff sub_matches_iff_render check_allow_iff
  check_allow_of_add_deny parsePattern_sub_valid
  Addr.Prefix.contains_iff Addr.ipv4Registry_blocks Addr.ipv6Registry_blocks Addr.contains_iff_range4
  Addr.contains_iff_range6 Addr.parse_render Addr.allows4_iff Addr.embeds_iff Addr.nat64Ok_iff
  Addr.allows6_iff Addr.check_allow_iff Addr.registry4_denied Addr.multicast4_denied Addr.registry6_denied
  Addr.outside_global_denied Addr.sixToFour_denied Addr.teredo_denied Addr.mapped_allows_iff
  Addr.mapped_denied Addr.nat64_allows_iff Addr.nat64_denied Addr.isatap_denied Addr.allows_of_add_deny4
  Addr.allows_of_add_deny6
  Addr.Prefix.contains_iff_getMsbD Addr.parse4_isSome_iff
  Addr.render6_canonical Addr.hex16_canonical
  Addr.explain_eq_none_iff Addr.parsePrefix_v4 Addr.parsePrefix_v6
  Addr.parse4_eq_some_iff Addr.allows_nat64_wellKnown"

# 1. Build configuration, checked before anything runs Lake (a lakefile is code that Lake executes).
#    Any change to these files must update the hashes here, in plain sight. Pinning them rules out
#    extra targets or libraries, another source directory, compiler or linker options, dependencies
#    and code in the lakefile.
pin() { [ "$(sha256sum "$1" | cut -d' ' -f1)" = "$2" ] || fail "$1 differs from the pinned version"; }
pin lakefile.lean e0a766dd6a4d4ce2c3352296896d0e9b3a57d8940e2ac3615f12717d943af684
pin lean-toolchain ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c
pin lake-manifest.json 1882a2ae901943eabe1cef70d85b772aa8852ea968d9279b66fc7f038b96ef39
[ ! -e lakefile.toml ] || fail "lakefile.toml must not exist"
if [ "${1:-}" = "--pins" ]; then echo "audit: pinned build configuration OK"; exit 0; fi

# 2. Source: no `sorry`/`admit`, `native_decide`, new axioms or opaque constants,
#    `implemented_by`/`extern`, `partial`/`unsafe` definitions, options that skip kernel checking,
#    `#eval`/`#exit`/`initialize`, or metaprograms that could change the environment. (`Main.lean` may
#    use `partial` to read stdin.)
files=$(find UrlFence.lean UrlFence -name '*.lean' | sort)
if grep -nE '\b(sorry|admit|native_decide|axiom|opaque|implemented_by|extern|partial|unsafe|run_tac|run_cmd|run_elab|run_meta|elab|elab_rules|macro|macro_rules|syntax|initialize|builtin_initialize|skipKernelTC)\b|#eval|#exit|set_option +debug' \
    $files; then
  fail "forbidden keyword in the library"
fi

# 3. Environment: imports, replaced implementations, axioms of every declaration, and the published
#    statements with the definitions they depend on.
out=$(lake env lean scripts/Axioms.lean)
! grep '^BADNAME ' <<<"$out" || fail "a library name contains whitespace"
canon_file=$(mktemp); trap 'rm -f "$canon_file"' EXIT
grep '^CANON ' <<<"$out" > "$canon_file"
# SHA-256 of a theorem's printed statement and the raw terms of everything it depends on.
depsha() {
  local deps n
  deps=$(grep -F "DEPS $1 " <<<"$out" | cut -d' ' -f3-) || return 1
  { grep -F "STATEMENT $1 : " <<<"$out"
    for n in $deps; do
      [ "$(awk -v n="$n" '$1 == "CANON" && $2 == n' "$canon_file" | wc -l)" = 1 ] || return 1
      awk -v n="$n" '$1 == "CANON" && $2 == n' "$canon_file"
    done
  } | sha256sum | cut -d' ' -f1
}
published_lines=""
for t in $PUBLISHED; do
  s=$(grep -F "STATEMENT UrlFence.$t : " <<<"$out") || fail "missing theorem UrlFence.$t"
  d=$(depsha "UrlFence.$t") || fail "missing dependencies for UrlFence.$t"
  published_lines+="$s"$'\n'"DEPSHA UrlFence.$t $d"$'\n'
done
if [ "${1:-}" = "--print-statements" ]; then printf '%s' "$published_lines"; exit 0; fi

bad_imports=$(grep '^IMPORT ' <<<"$out" | awk '$3 !~ /^(Init|UrlFence)([.]|$)/' || true)
[ -z "$bad_imports" ] || fail "the library imports other modules: $bad_imports"
! grep -E '^(IMPLBY|EXTERN) ' <<<"$out" || fail "compiled code of a library declaration is replaced"
lines=$(grep '^AXIOMS ' <<<"$out" || true)
[ -n "$lines" ] || fail "no declarations listed"
! grep -E '^AXIOMS (axiom|opaque) ' <<<"$lines" || fail "the library declares an axiom or opaque constant"
bad=$(sed -E 's/^AXIOMS [a-z]+ [^ ]+: \[(.*)\]$/\1/' <<<"$lines" | tr ',' '\n' | tr -d ' ' | grep -v '^$' \
  | grep -vxE 'propext|Classical\.choice|Quot\.sound' | sort -u || true)
[ -z "$bad" ] || fail "non-standard axioms: $bad"

# The published theorems must exist with exactly the reviewed statements and dependency hashes: a
# renamed theorem, a weakened statement or a changed definition behind it fails here.
if ! diff <(printf '%s' "$published_lines") scripts/statements.expected >/dev/null; then
  diff <(printf '%s' "$published_lines") scripts/statements.expected >&2 || true
  fail "published statements or the definitions they depend on differ from scripts/statements.expected"
fi
thms=$(grep -c '^AXIOMS theorem ' <<<"$lines")
decls=$(wc -l <<<"$lines")
imports=$(grep -c '^IMPORT ' <<<"$out")
published=$(wc -w <<<"$PUBLISHED")

# 4. The kernel's own checker replays every module.
lake env leanchecker UrlFence >/dev/null || fail "leanchecker rejected a module"

echo "audit: OK ($decls declarations, $thms theorems, standard axioms only; $published published statements and their definitions unchanged; $imports imports, all Init or UrlFence; no replaced implementations; pinned build configuration; leanchecker passed)"
