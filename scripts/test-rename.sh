#!/bin/sh
# test-rename.sh — regression test for `lean-refactor rename d r` on a structure field.
#
# `scripts/fixtures/rename` declares two fields with the same last component
# (`Fix.Alg.PowerAllegory.powerObj`, `Fix.HasPowerObject.powerObj`).  Renaming the first must
# (a) leave every use of the second alone — uses are the resolved constant, never the identifier
# text; (b) write each use in the shortest spelling that resolves to the new constant in that
# file's scope, keeping the source's own spelling where it still resolves; (c) respell dotted and
# `@` uses.  The run is APPLIED, so the capped build checks the result elaborates.
#
# Builds the fixture in a scratch copy (so `.lake` never lands in the checked-in fixture).
set -e
root=$(dirname "$(dirname "$(readlink -f "$0")")")
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
cp -r "$root/scripts/fixtures/rename"/. "$work"/
cd "$work"
"$root/scripts/cap" lake build -q Fix
out=$("$root/scripts/lean-refactor" rename Fix.Alg.PowerAllegory.powerObj Fix.Alg.PowerAllegory.P --apply)
echo "$out"
base=$(cat Fix/Base.lean); use=$(cat Fix/Use.lean); short=$(cat Fix/Short.lean)

fail=0
check() {
  case "$1" in
    *"$2"*) ;;
    *) echo "test-rename: MISSING \`$2\`"; fail=1 ;;
  esac
}
check "$base" '  P : α → α'
check "$base" '  powerObj_idem : ∀ a, P (P a) = P a'
check "$base" '  powerObj : α → α
  powerObj_idem : ∀ a, powerObj (powerObj a) = powerObj a'
check "$use" 'def qualified : α := PowerAllegory.P a'
check "$use" 'def explicit : α := @PowerAllegory.P α _ a'
check "$use" 'def dotted (inst : PowerAllegory α) : α := inst.P a'
check "$use" 'def otherDotted (h : HasPowerObject α) : α := h.powerObj a'
check "$use" 'def otherQualified (h : HasPowerObject α) : α := HasPowerObject.powerObj h a'
check "$short" 'def opened : α := P a'
check "$short" 'def full : α := Fix.Alg.PowerAllegory.P a'

if [ "$fail" = 0 ]; then echo "test-rename: PASS"; else echo "test-rename: FAIL"; exit 1; fi
