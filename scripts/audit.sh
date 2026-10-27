#!/usr/bin/env bash
# Proof audit: no escape hatches in the library, only Lean's standard axioms behind any of its
# declarations, no other code reaching it, compiled code that is the proven code, and every module
# accepted by the kernel's own checker.
#
# What this does not check: that Main.lean (the CLI) calls the library as documented. That is
# ordinary code, covered by review and by the tests.
set -euo pipefail
cd "$(dirname "$0")/.."

fail() { echo "audit: $*" >&2; exit 1; }

# 1. Source: no `sorry`/`admit`, `native_decide`, new axioms or opaque constants,
#    `implemented_by`/`extern`, `partial`/`unsafe` definitions, options that skip kernel checking,
#    `#eval`/`initialize`, or metaprograms that could change the environment. (`Main.lean` may use
#    `partial` to read stdin.)
files=$(find UrlFence.lean UrlFence -name '*.lean' | sort)
if grep -nE '\b(sorry|admit|native_decide|axiom|opaque|implemented_by|extern|partial|unsafe|run_tac|run_cmd|run_elab|run_meta|elab|elab_rules|macro|macro_rules|syntax|initialize|builtin_initialize|skipKernelTC)\b|#eval|set_option +debug' \
    $files; then
  fail "forbidden keyword in the library"
fi

# 2. Build configuration: one library and one executable, nothing else compiled into the package,
#    no dependencies, no extra compiler options.
if grep -nE '\b(require|leanOptions|moreLeanArgs|moreServerArgs|moreLinkArgs|weakLeanArgs|extern_lib|target|input_file|input_dir|precompileModules|plugins|dynlibs|needs)\b' lakefile.lean; then
  fail "unexpected build configuration in lakefile.lean"
fi
[ "$(grep -cE '^\s*lean_lib\b' lakefile.lean)" = 1 ] && grep -qE '^\s*lean_lib UrlFence\s*$' lakefile.lean \
  || fail "lakefile.lean must declare exactly the library UrlFence"
[ "$(grep -cE '^\s*lean_exe\b' lakefile.lean)" = 1 ] || fail "lakefile.lean must declare exactly one executable"

# 3. Environment: imports, replaced implementations, and axioms of every declaration.
out=$(lake env lean scripts/Axioms.lean)
bad_imports=$(grep '^IMPORT ' <<<"$out" | awk '$3 !~ /^(Init|UrlFence)([.]|$)/' || true)
[ -z "$bad_imports" ] || fail "the library imports other modules: $bad_imports"
! grep -E '^(IMPLBY|EXTERN) ' <<<"$out" || fail "compiled code of a library declaration is replaced"
lines=$(grep '^AXIOMS ' <<<"$out" || true)
[ -n "$lines" ] || fail "no declarations listed"
! grep -E '^AXIOMS (axiom|opaque) ' <<<"$lines" || fail "the library declares an axiom or opaque constant"
bad=$(sed -E 's/^AXIOMS [a-z]+ [^ ]+: \[(.*)\]$/\1/' <<<"$lines" | tr ',' '\n' | tr -d ' ' | grep -v '^$' \
  | grep -vxE 'propext|Classical\.choice|Quot\.sound' | sort -u || true)
[ -z "$bad" ] || fail "non-standard axioms: $bad"

# The published theorems must all be there (a rename would otherwise drop one silently).
for t in join_split split_join split_append_sep join_append parseHost_render parseHost_valid domainOk_noDot parseScheme_spec splitPort_spec parse_render parse_valid parse_no_userinfo sub_not_ipv4 sub_matches_iff sub_matches_iff_render check_allow_iff check_allow_of_add_deny parsePattern_sub_valid; do
  grep -q "^AXIOMS theorem UrlFence\.$t: " <<<"$lines" || fail "missing theorem UrlFence.$t"
done
thms=$(grep -c '^AXIOMS theorem ' <<<"$lines")
decls=$(wc -l <<<"$lines")
imports=$(grep -c '^IMPORT ' <<<"$out")

# 4. The kernel's own checker replays every module.
lake env leanchecker UrlFence >/dev/null || fail "leanchecker rejected a module"

echo "audit: OK ($decls declarations, $thms theorems, standard axioms only; $imports imports, all Init or UrlFence; no replaced implementations; leanchecker passed)"
