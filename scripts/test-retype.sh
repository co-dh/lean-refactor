#!/bin/sh
# test-retype.sh — regression test for `lean-refactor retype A B [--convert g]`.
#
# `scripts/fixtures/retype` is the state right after a field changed type: `Fix/Base.lean` has
# `Vec.count : USize` and builds.  `Fix/Use.lean` holds every site a retype fixes: a binder, a group
# split, a caller retyped in the next round, a result type, `fun`/`let`/`∃` binders, a `variable` all
# its declarations want, and a retyped binder used as a `Nat` (converted by `--convert`).
# `Fix/Left.lean` holds every site retype must leave and report: a structure field, a term that is no
# variable, a pattern-bound and an auto-bound variable, a `variable` one declaration disagrees with,
# and a retype that causes an error of another kind.  `Fix/Down.lean` (imports `Use`) is elaborated
# only once `Use` has been written and built.
#
# Builds the fixture in a scratch copy (so `.lake` never lands in the checked-in fixture).
set -e
root=$(dirname "$(dirname "$(readlink -f "$0")")")
work=$(mktemp -d "${TMPDIR:-/tmp}/test-retype.XXXXXX")
trap 'rm -rf "$work"' EXIT
cp -r "$root/scripts/fixtures/retype"/. "$work"/
cd "$work"
"$root/scripts/cap" lake build -q Fix.Base
original=$(cat Fix/Use.lean)
preview=$("$root/scripts/lean-refactor" retype Nat USize)
echo "$preview"
[ "$(cat Fix/Use.lean)" = "$original" ] || { echo "test-retype: the preview wrote Fix/Use.lean"; exit 1; }
set +e
applied_log=$("$root/scripts/lean-refactor" retype Nat USize --convert USize.toNat --apply 2>&1)
status=$?
set -e
echo "$applied_log"
# `Fix/Left.lean` keeps the sites it reports, so its build fails and the run says so in its status.
[ "$status" = 1 ] || { echo "test-retype: --apply exited $status, expected 1 for Fix/Left.lean"; exit 1; }
use=$(cat Fix/Use.lean)
left=$(cat Fix/Left.lean)
down=$(cat Fix/Down.lean)

fail=0
check() {
  case "$1" in
    *"$2"*) ;;
    *) echo "test-retype: MISSING \`$2\`"; fail=1 ;;
  esac
}
check "$preview" 'Fix/Down.lean: not elaborated: it imports Fix.Use, which has rewrites that only --apply writes'
check "$preview" 'Fix/Use.lean:8: `n`, retyped to USize, is used where Nat is needed; left for coerce'
check "$preview" 'retype "(n m : Nat)" -> "(n : USize) (m : Nat)"'
check "$preview" 'Fix/Left.lean:8:29: a USize given to a field of type Nat of Old.mk: a representation decision, reported only'
check "$preview" 'Fix/Left.lean:9:33: `(take k)` is no variable; left for coerce'
check "$preview" 'Fix/Left.lean:11:17: `n`: bound by a pattern; left for coerce or by hand'
check "$preview" 'Fix/Left.lean:13:33: `n` has no written binder (auto-bound); left for coerce or by hand'
check "$preview" 'Fix/Left.lean:14:53: error after the rewrite'
check "$preview" 'Fix/Left.lean:14:70: `n`: retyping its binder was dropped by the error check'
check "$preview" 'Fix/Left.lean:17:10: variable `z` is wanted as USize by 1 of the 2 declarations binding it; not retyped'
check "$applied_log" 'Fix/Use.lean:8: convert "n" -> "n.toNat"'
check "$use" 'def single (n : USize) : Vec := mk n'
check "$use" 'def group (n : USize) (m : Nat) : Vec'
check "$use" 'def caller (k : USize) : Vec := single k'
check "$use" 'def needs (n : USize) : Vec × Nat := (mk n, take n.toNat)'
check "$use" 'def body (v : Vec) : USize := v.count'
check "$use" 'def lam : Vec := (fun (n : USize) => mk n) 3'
check "$use" 'def letb : Vec := let n : USize := 3; mk n'
check "$use" 'theorem ex : ∃ n : USize, (mk n).name = "v"'
check "$use" 'variable (w : USize)'
check "$left" 'variable (z : Nat)'
check "$left" 'def other (n : Nat) : Vec'
check "$left" 'def field : Old := { size := usz }'
check "$down" 'def down (j : USize) : Vec := single j'

if [ "$fail" = 0 ]; then echo "test-retype: PASS"; else echo "test-retype: FAIL"; exit 1; fi
