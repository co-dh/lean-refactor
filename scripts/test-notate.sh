#!/bin/sh
# test-notate.sh — regression test for `lean-refactor notate d --form f`.
#
# `scripts/fixtures/notate` uses one class method in every spelling the info trees resolve to the
# same constant — dotted, through `open`, `@`-explicit — as an infix operand, as a bracketed argument,
# and nested in itself.  `P $0` must bracket a compound argument and keep the brackets an application
# needs; `P[$0]` must drop both.  The `P $0` run is APPLIED, so the capped build checks the result
# elaborates; the `P[$0]` run is a preview.
#
# Builds the fixture in a scratch copy (so `.lake` never lands in the checked-in fixture).
set -e
root=$(dirname "$(dirname "$(readlink -f "$0")")")
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
cp -r "$root/scripts/fixtures/notate"/. "$work"/
cd "$work"
"$root/scripts/cap" lake build -q Fix
d=Fix.Alg.PowerAllegory.powerObj
preview=$("$root/scripts/lean-refactor" notate $d --form 'P[$0]' --in Fix/Use.lean)
echo "$preview"
"$root/scripts/lean-refactor" notate $d --form 'P $0' --in Fix/Use.lean --apply
applied=$(cat Fix/Use.lean)

fail=0
check() {
  case "$1" in
    *"$2"*) ;;
    *) echo "test-notate: MISSING \`$2\`"; fail=1 ;;
  esac
}
check "$preview" '"(PowerAllegory.powerObj (f a))" -> "P[f a]"'
check "$preview" '"powerObj a" -> "P[a]"'
check "$preview" '"@PowerAllegory.powerObj α _ a" -> "P[a]"'
check "$preview" '"(powerObj a)" -> "P[a]"'
check "$preview" '-> "P[P[b]]"'
check "$applied" 'def dotted : α := P (f a)'
check "$applied" 'def opened : Type := P a ⟶ b'
check "$applied" 'def explicit : α := P a'
check "$applied" 'def inArg : α := f (P a)'
check "$applied" 'def nested : α := f (P (P b))'

if [ "$fail" = 0 ]; then echo "test-notate: PASS"; else echo "test-notate: FAIL"; exit 1; fi
