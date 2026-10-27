#!/usr/bin/env bash
# Rebuild and re-check URLFence from a fresh clone of this checkout's HEAD, in a temporary
# directory, so that nothing local (an old build, uncommitted files) affects the result.
#
#   ./scripts/reproduce.sh          # what CI runs, with the full corpus for the client comparison
#
# Needs git, elan (for the pinned toolchain), python3, node and curl, and fails without them, as CI
# does. urllib3 and requests are compared only if they are installed; a client that is missing is
# reported as skipped, never as passing.
set -euo pipefail

for t in git lake python3 node curl sha256sum; do
  command -v "$t" >/dev/null || { echo "reproduce: $t not found" >&2; exit 1; }
done
# Test the binary built here (tests/common.py honours URLFENCE_BIN), with the pinned toolchain.
unset URLFENCE_BIN ELAN_TOOLCHAIN

src=$(git -C "$(dirname "$0")/.." rev-parse --show-toplevel)
head=$(git -C "$src" rev-parse HEAD)
if [ -n "$(git --no-optional-locks -C "$src" status --porcelain)" ]; then
  echo "reproduce: uncommitted changes and untracked files in $src are not included" >&2
fi
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
export TMPDIR="$work"  # the steps' temporary files (the mutation check's copy) go with it

git clone --quiet --no-local --no-checkout "$src" "$work/urlfence"
cd "$work/urlfence"
git -c advice.detachedHead=false checkout --quiet "$head"
echo "== URLFence $(git rev-parse --short HEAD), $(cat lean-toolchain)"

step() { echo; echo "== $*"; }
step "pinned build configuration (before anything runs Lake)"
./scripts/audit.sh --pins
step "build"
lake build
step "proof audit"
./scripts/audit.sh
step "tests"
python3 -m unittest discover -s tests
step "client comparison: self-test, then the full corpus"
python3 tests/compat.py --self-test --require whatwg,node,urlsplit,urllib.request,curl
python3 tests/compat.py --require whatwg,node,urlsplit,urllib.request,curl
step "mutation check"
python3 tests/mutants.py

step "done: every step passed"
sha256sum .lake/build/bin/urlfence
