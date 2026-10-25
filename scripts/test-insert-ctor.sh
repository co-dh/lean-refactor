#!/bin/sh
# test-insert-ctor.sh — regression test: `insert-arg C.mk n term` reaches every construction and
# pattern of the structure, whatever its spelling, from the info trees.
#
# `scripts/fixtures/insert-ctor` writes `Col` as `⟨…⟩` in terms and in `match`, `fun`, `let`,
# `if let` and `for` patterns, as `Col.mk …` and `.mk …`, as a named-field instance and a `with`
# update, and destructs it with `obtain`.  The field is declared FIRST, as a refactor would: every
# other file is then read against the built (old) `Col`, and the declaring file, whose `⟨…⟩` no
# longer elaborates, by its expected type.  The edit is APPLIED, so its own build checks the result.
set -e
root=$(dirname "$(dirname "$(readlink -f "$0")")")
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
cp -r "$root/scripts/fixtures/insert-ctor"/. "$work"/
cd "$work"
"$root/scripts/cap" lake build -q Ctor
sed -i 's/^  enc : Enc$/  enc : Enc\n  d : Nat := 7/' Ctor/Base.lean
"$root/scripts/lean-refactor" insert-arg Ctor.Col.mk 4 9 --in 'Ctor/*.lean' --apply
base=$(cat Ctor/Base.lean); use=$(cat Ctor/Use.lean)

fail=0
check() {
  case "$1" in
    *"$2"*) ;;
    *) echo "test-insert-ctor: MISSING \`$2\`"; fail=1 ;;
  esac
}
check "$base" 'def inFile : Col := ⟨0, 1, .raw 2, 9⟩'
check "$use" 'def anonTerm (t : Nat) : Col := ⟨t, 2, .raw 3, 9⟩'
check "$use" 'some ⟨1, 2, .packed 3 4, 9⟩'
check "$use" 'Col.mk 1 2 (.raw 0) 9'
check "$use" ':= .mk 1 2 (.raw 0) 9'
check "$use" '{ ty := 1, n := 2, enc := .raw 0 }'
check "$use" '{ c with n := 5 }'
check "$use" '| ⟨_, _, .packed a b, _⟩ => a + b'
check "$use" '| ⟨t, _, .raw m, _⟩ => t + m'
check "$use" '| .mk t n _ _ => t + n'
check "$use" 'fun ⟨t, _, _, _⟩ => t'
check "$use" 'let ⟨_, n, _, _⟩ := c; n'
check "$use" 'if let ⟨t, _, .raw _, _⟩ := c'
check "$use" 'for ⟨t, _, _, _⟩ in cs'
check "$use" 'obtain ⟨t, n, e⟩ := c'
check "$use" '(⟨1, 2, .raw 0, 9⟩ : Col).n'

# A parameter WITH a default: terms that omit it keep the default and are not edited; a pattern
# takes `_` (there the default would be a pattern too), and one short of it names the parameter.
sed -i 's/^@\[match_pattern\] abbrev V.gen (k : Nat) (n : Nat := 0) : V := .vec k n none$/@[match_pattern] abbrev V.gen (k : Nat) (n : Nat := 0) (a : Option Nat := none) : V := .vec k n a/' Ctor/Base.lean
"$root/scripts/lean-refactor" insert-arg Ctor.V.gen 3 none --in 'Ctor/*.lean' --apply
use=$(cat Ctor/Use.lean)
check "$use" '| .gen k n _ => k + n'
check "$use" '| .gen k (a := _) => k'
check "$use" 'def genTerm1 : V := .gen 1
'
check "$use" 'def genTerm2 : V := V.gen 1 2
'
check "$use" 'def genMap : List V := [1, 2].map V.gen
'
exit $fail
