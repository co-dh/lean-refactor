#!/bin/sh
# test-occurrences.sh — regression test: an occurrence of a declaration is what the elaborator
# resolved to that CONSTANT, never an identifier spelled like it.
#
# `scripts/fixtures/occurrences` holds, beside real uses:
# (a) for `remove-arg Fix.cost 1 --syntax`: a local `fun cost => …` and a binder `(cost : …)` applied
#     like the constant, `h cost` with the constant as an ARGUMENT, and `(graph (cost tc) : Nat)`,
#     whose duplicated edit once spliced `(graph costour City`;
# (b) for `rename Fix.Q Fix.Qbook`: named arguments `(Q := e)` and structure fields `{ Q := e }`,
#     whose key is the callee's binder or the structure's field, not the constant `Fix.Q`; their
#     values are terms and do move.
# The rename is APPLIED, so its own elaboration check confirms the result compiles.
set -e
root=$(dirname "$(dirname "$(readlink -f "$0")")")
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
cp -r "$root/scripts/fixtures/occurrences"/. "$work"/
cd "$work"
"$root/scripts/cap" lake build -q Fix
"$root/scripts/lean-refactor" rename Fix.Q Fix.Qbook --apply
"$root/scripts/lean-refactor" remove-arg Fix.cost 1 --syntax --in Fix/Use.lean --apply
base=$(cat Fix/Base.lean); use=$(cat Fix/Use.lean)

fail=0
check() {
  case "$1" in
    *"$2"*) ;;
    *) echo "test-occurrences: MISSING \`$2\`"; fail=1 ;;
  esac
}
check "$base" 'def Qbook : Nat := 0'
check "$base" 'def call (Q : Nat) (P : Nat := 0) : Nat := Q + P'
check "$base" '  Q : Nat'
check "$use" 'def named : Nat := call (Q := Qc)'
check "$use" 'def namedValue : Nat := call (P := Qbook) (Q := Qc)'
check "$use" 'def namedExplicit : Nat := @call (Q := Qbook) (P := 1)'
check "$use" 'def fields : Pair := { Q := Qbook, P := 1 }'
check "$use" 'def letSameName : Nat := let Q := 4; Q + Fix.Qbook'
check "$use" 'def ascribed (tc : Nat → Nat) : Nat := (graph cost : Nat)'
check "$use" 'def full (tc : Nat → Nat) : Nat := cost 5'
check "$use" 'def nested (h : (Nat → Nat) → Nat) : Nat := h cost'
check "$use" ':= fun cost => cost id 1'
check "$use" 'def boundSameName (cost : (Nat → Nat) → Nat → Nat) : Nat := cost id 2'
check "$use" 'def unapplied (h : ((Nat → Nat) → Nat → Nat) → Nat) : Nat := h cost'

if [ "$fail" = 0 ]; then echo "test-occurrences: PASS"; else echo "test-occurrences: FAIL"; exit 1; fi
