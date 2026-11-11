#!/bin/sh
# test-coerce.sh — regression test for `lean-refactor coerce (A B f)...`.
#
# `scripts/fixtures/coerce` is the state right after a field changed type: `Fix/Base.lean` has
# `Vec.count : USize` and builds, while `Fix/Use.lean`, `Fix/Other.lean` and `Fix/Down.lean` (which
# imports `Use`) still treat it as a `Nat`.  Every Nat→USize and USize→Nat meeting must be converted:
# an argument either way, a body, a structure field, an argument that needs brackets, nested sites;
# `Down` only once `Use` has been written and built (import order).  A site under a notation is
# reported and left, and an unrelated error is left and reported with file:line.
#
# Builds the fixture in a scratch copy (so `.lake` never lands in the checked-in fixture).
set -e
root=$(dirname "$(dirname "$(readlink -f "$0")")")
work=$(mktemp -d "${TMPDIR:-/tmp}/test-coerce.XXXXXX")
trap 'rm -rf "$work"' EXIT
cp -r "$root/scripts/fixtures/coerce"/. "$work"/
cd "$work"
"$root/scripts/cap" lake build -q Fix.Base
conv='Nat USize Nat.toUSize USize Nat USize.toNat'
original=$(cat Fix/Use.lean)
preview=$("$root/scripts/lean-refactor" coerce $conv)
echo "$preview"
[ "$(cat Fix/Use.lean)" = "$original" ] || { echo "test-coerce: the preview wrote Fix/Use.lean"; exit 1; }
set +e
applied_log=$("$root/scripts/lean-refactor" coerce $conv --apply 2>&1)
status=$?
set -e
echo "$applied_log"
# `Fix/Other.lean` keeps its unrelated error, so its build fails and the run says so in its status.
[ "$status" = 1 ] || { echo "test-coerce: --apply exited $status, expected 1 for Fix/Other.lean"; exit 1; }
use=$(cat Fix/Use.lean)
other=$(cat Fix/Other.lean)
down=$(cat Fix/Down.lean)

fail=0
check() {
  case "$1" in
    *"$2"*) ;;
    *) echo "test-coerce: MISSING \`$2\`"; fail=1 ;;
  esac
}
check "$preview" 'Fix/Down.lean: not elaborated: it imports Fix.Use, which has rewrites that only --apply writes'
check "$preview" 'site in a macro or notation expansion'
check "$preview" 'Fix/Other.lean:6:23: error remains, as before the rewrite'
check "$use" 'def natArg (n : Nat) : Vec := mk n.toUSize'
check "$use" 'def usizeArg (v : Vec) : Nat := take v.count.toNat'
check "$use" 'def bracketed (n : Nat) : Vec := mk <| (take n).toUSize'
check "$use" 'def body (v : Vec) : Nat := v.count.toNat'
check "$use" '{ count := n.toUSize, name := "x" }'
check "$use" 'twice (take (size (mk n.toUSize))).toUSize'
check "$other" 'def underNotation (n : Nat) : Vec := MK n'
check "$other" 'def notationArg : Vec := mk (SEVEN).toUSize'
check "$other" 'def unrelated : Nat := "oops"'
check "$other" 'def plain (n : Nat) : Vec := mk n.toUSize'
check "$down" 'take (natArg n).count.toNat'

if [ "$fail" = 0 ]; then echo "test-coerce: PASS"; else echo "test-coerce: FAIL"; exit 1; fi
