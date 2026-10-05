#!/bin/sh
# test-collapse.sh — regression test for `lean-refactor collapse d r`.
#
# `scripts/fixtures/collapse` declares `Fix.Alg.RelSet.Edit.leqN`, a duplicate of
# `Fix.Alg.RelSet.leRel`, and names it in another file inside attribute syntax
# (`@[app_unexpander …]`, `attribute [local simp] …`).  Collapsing must (a) rewrite those attribute
# arguments like any other use, in every file, and (b) write the survivor in the shortest spelling
# that resolves to it at the site — `leRel` inside `namespace Fix.Alg.RelSet.Edit` and after
# `open Fix.Alg.RelSet`, `Alg.RelSet.leRel` inside `namespace Fix.Use`.  The run is APPLIED, so the capped
# build checks the result elaborates.
#
# Builds the fixture in a scratch copy (so `.lake` never lands in the checked-in fixture).
set -e
root=$(dirname "$(dirname "$(readlink -f "$0")")")
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
cp -r "$root/scripts/fixtures/collapse"/. "$work"/
cd "$work"
"$root/scripts/cap" lake build -q Fix
out=$("$root/scripts/lean-refactor" collapse Fix.Alg.RelSet.Edit.leqN Fix.Alg.RelSet.leRel --apply)
echo "$out"
base=$(cat Fix/Base.lean); use=$(cat Fix/Use.lean)

fail=0
check() {
  case "$1" in
    *"$2"*) ;;
    *) echo "test-collapse: MISSING \`$2\`"; fail=1 ;;
  esac
}
absent() {
  case "$1" in
    *"$2"*) echo "test-collapse: STILL PRESENT \`$2\`"; fail=1 ;;
  esac
}
check "$base" 'theorem leqN_refl (a : Nat) : leRel a a := Nat.le_refl a'
absent "$base" 'leqN (a b'
absent "$base" 'The duplicate'
check "$use" '@[app_unexpander Alg.RelSet.leRel] def unexpLeqN'
check "$use" 'attribute [local simp] leRel'
check "$use" 'example : leRel 1 1 := Nat.le_refl 1'

if [ "$fail" = 0 ]; then echo "test-collapse: PASS"; else echo "test-collapse: FAIL"; exit 1; fi
