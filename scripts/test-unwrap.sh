#!/bin/sh
# test-unwrap.sh — regression test for `lean-refactor unwrap d`.
#
# `scripts/fixtures/unwrap` builds against `Fix/Base.lean`, whose `step`, `look` and `Box.get` return
# `Except`/`Option`; the test then swaps in `Base.total`, where they return the plain value, so
# `Fix/Use.lean` fails before the operation — the state `unwrap` is for.  Every rewrite form in every
# spelling (opened, qualified, `@`, named arguments, a call over three lines, dotted, `|>.`, bracketed)
# must be rewritten; a call where the elaborator still expects `Except`/`Option` (a body, a `do` value,
# a `match` or `if` branch, a `fun` body, an argument, a structure field) becomes `pure (…)`; a `match`
# on the call keeps its success alternatives without the constructor and drops the failure ones; a
# projection is listed as unrecognised and a `simp [step]` as a mention; the rewrite in
# `gateDrops` makes a new error (`Except.ok.inj` on a plain equation), so the gate must drop it.
#
# Builds the fixture in a scratch copy (so `.lake` never lands in the checked-in fixture).
set -e
root=$(dirname "$(dirname "$(readlink -f "$0")")")
work=$(mktemp -d "${TMPDIR:-/tmp}/test-unwrap.XXXXXX")
trap 'rm -rf "$work"' EXIT
cp -r "$root/scripts/fixtures/unwrap"/. "$work"/
cd "$work"
"$root/scripts/cap" lake build -q Fix
cp Base.total Fix/Base.lean
"$root/scripts/cap" lake build -q Fix.Base
original=$(cat Fix/Use.lean)
preview=$("$root/scripts/lean-refactor" unwrap Fix.Ops.step --in Fix/Use.lean)
echo "$preview"
[ "$(cat Fix/Use.lean)" = "$original" ] || { echo "test-unwrap: the preview wrote Fix/Use.lean"; exit 1; }
"$root/scripts/lean-refactor" unwrap Fix.Ops.step --in Fix/Use.lean --apply
"$root/scripts/lean-refactor" unwrap Fix.Ops.look --in Fix/Use.lean --apply
"$root/scripts/lean-refactor" unwrap Fix.Ops.Box.get --in Fix/Use.lean --apply
applied=$(cat Fix/Use.lean)

fail=0
check() {
  case "$1" in
    *"$2"*) ;;
    *) echo "test-unwrap: MISSING \`$2\`"; fail=1 ;;
  esac
}
check "$preview" 'unrecognised, left as is: the call sits inside'
check "$preview" 'error after the rewrite'
check "$preview" '"←" -> ":="'
check "$preview" '"← " -> ""'
check "$applied" '  let x := step a 1'
check "$applied" '  let x := Fix.Ops.step a 2'
check "$applied" '  return (step a 3) + 1'
check "$applied" '  let x := @step a 4'
check "$applied" '  let x := step (b := 5) (a := a)'
check "$applied" '  let x := step
    a
    6'
check "$applied" '  x := step x 7'
check "$applied" '  let r := step a 8
  pure r'
check "$applied" 'def letSome (k : Nat) : Nat := Id.run do
  let r := look k
  return r'
check "$applied" 'def letSomeQualified (k : Nat) : Nat := Id.run do
  let r := look k
  return r'
check "$applied" '  let x := b.get 1'
check "$applied" '  let x := b |>.get 2'
check "$applied" 'step a 0 = a :='
check "$applied" '(h : step a 1 = (a + 1))'
check "$applied" 'step a 2 = (a + 2) :='
check "$applied" 'look k = k :='
check "$applied" 'k = look k :='
check "$applied" '(b.get 3) = (b.n + 3) :='
check "$applied" '  match step a 9 with
  | r => r

theorem'
check "$applied" '  match look k with
  | r => r + 1'
check "$applied" ':= pure (step a 13)'
check "$applied" '  let y := a
  pure (step y 14)'
check "$applied" '  | true => pure (step a 15)'
check "$applied" '  if b then pure (step a 16) else .ok a'
check "$applied" 'fun a => pure (step a 17)'
check "$applied" 'Except.map id (pure (step a 18))'
check "$applied" '{ v := pure (step a 19) }'
check "$applied" ':= pure (look (k + 1))'
check "$applied" '(step a 12).toBool'
check "$preview" 'unrecognised, left as is: the call sits inside `Lean.Parser.Term.proj`'
check "$preview" 'mention, no rewrite (1)'
check "$applied" '(h : step a 11 = .ok 0)'

if [ "$fail" = 0 ]; then echo "test-unwrap: PASS"; else echo "test-unwrap: FAIL"; exit 1; fi
