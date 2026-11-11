#!/bin/sh
# test-uncoerce.sh — regression test for `lean-refactor uncoerce (A B f)...`.
#
# `scripts/fixtures/uncoerce` is the state right after binders went from `Nat` to `USize`: `Fix/Use.lean`
# still converts with `Nat.toUSize`/`USize.toNat`.  Each redundant conversion must go: the dead field
# `n.toUSize`, the spelled `Nat.toUSize n`, `n.toNat` where a `USize` is expected (an argument, a body,
# in brackets), brackets the parse needs kept, nested sites, and the proved round trip `n.toNat.toUSize`
# in one run.  The lossy round trip stays, a site whose removal leaves an error is dropped by the gate,
# a site under a notation is reported, and an unrelated error is reported with file:line.
#
# Builds the fixture in a scratch copy (so `.lake` never lands in the checked-in fixture).
set -e
root=$(dirname "$(dirname "$(readlink -f "$0")")")
work=$(mktemp -d "${TMPDIR:-/tmp}/test-uncoerce.XXXXXX")
trap 'rm -rf "$work"' EXIT
cp -r "$root/scripts/fixtures/uncoerce"/. "$work"/
cd "$work"
"$root/scripts/cap" lake build -q Fix.Base
conv='Nat USize Nat.toUSize USize Nat USize.toNat'
original=$(cat Fix/Use.lean)
preview=$("$root/scripts/lean-refactor" uncoerce $conv)
echo "$preview"
[ "$(cat Fix/Use.lean)" = "$original" ] || { echo "test-uncoerce: the preview wrote Fix/Use.lean"; exit 1; }
set +e
applied_log=$("$root/scripts/lean-refactor" uncoerce $conv --apply 2>&1)
status=$?
set -e
echo "$applied_log"
# `Fix/Use.lean` keeps its unrelated error, so its build fails and the run says so in its status.
[ "$status" = 1 ] || { echo "test-uncoerce: --apply exited $status, expected 1 for Fix/Use.lean"; exit 1; }
use=$(cat Fix/Use.lean)

fail=0
check() {
  case "$1" in
    *"$2"*) ;;
    *) echo "test-uncoerce: MISSING \`$2\`"; fail=1 ;;
  esac
}
check "$preview" 'redundant conversion in a macro or notation expansion'
check "$preview" 'Fix/Use.lean:16:23: error remains, as before the rewrite'
check "$preview" 'error after the rewrite'
check "$preview" 'simp does not prove USize.toNat (Nat.toUSize y) = y; that round trip is kept'
check "$use" 'def dotted (n : USize) : Vec := mk n'
check "$use" 'def spelled (n : USize) : Vec := mk n'
check "$use" 'def expected (n : USize) : USize := ans n'
check "$use" 'def body (n : USize) : USize := n'
check "$use" 'def paren (n : USize) : USize := ans n'
check "$use" 'def arith (a b : USize) : USize := ans (a + b)'
check "$use" 'def chain (n : USize) : USize := ans n'
check "$use" 'def trip (n : USize) : USize := ans n'
check "$use" 'def lossy (n : Nat) : Nat := take (Nat.toUSize n).toNat'
check "$use" 'def still (n : USize) : Nat := take n.toUSize'
check "$use" 'def viaNotation (n : USize) : Vec := mk (TOU n)'

if [ "$fail" = 0 ]; then echo "test-uncoerce: PASS"; else echo "test-uncoerce: FAIL"; exit 1; fi
