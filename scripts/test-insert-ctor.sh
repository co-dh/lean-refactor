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
sed -i 's/^@\[match_pattern\] abbrev V.gen (k : Nat) (n : Nat := 0) : V := .vec ⟨n, .pay k, none⟩$/@[match_pattern] abbrev V.gen (k : Nat) (n : Nat := 0) (a : Option Nat := none) : V := .vec ⟨n, .pay k, a⟩/' Ctor/Base.lean
# A source ahead of its build (`VC` has three fields there) fails to elaborate, and its patterns
# record nothing: refused, where it used to leave both `.gen` patterns out without a word.
cp Ctor/Use.lean Ctor/Use.lean.orig
printf 'def genStale : V → Nat\n  | .pair (.vec ⟨_, _, _, _⟩) (.gen k _) => k\n  | .wrap _ (.gen k _) => k\n  | _ => 0\n' >> Ctor/Use.lean
if out=$("$root/scripts/lean-refactor" insert-arg Ctor.V.gen 3 none --in 'Ctor/*.lean' 2>&1); then
  echo "test-insert-ctor: a file that does not elaborate against its build was not refused"; fail=1
fi
check "$out" 'does not elaborate against the built imports'
mv Ctor/Use.lean.orig Ctor/Use.lean
"$root/scripts/lean-refactor" insert-arg Ctor.V.gen 3 none --in 'Ctor/*.lean' --apply
use=$(cat Ctor/Use.lean)
check "$use" '| .gen k n _ => k + n'
check "$use" '| .gen k (a := _) => k'
# Every pattern position, including those nested under another constructor, where the info tree
# keeps nothing once `.gen` is unfolded: each must name the new parameter.
check "$use" '| .wrap _ (.gen k n _) => k + n'
check "$use" '| .wrap _ (v@(.gen _ _ _)) => genBoth v'
check "$use" '| _, .atom k | _, .wrap _ (.gen k _ _) => k'
check "$use" '| .gen k n _, _ => return k + n'
check "$use" '| .gen k n _ => k + n + t'
check "$use" '| .gen k _ _ => k
'
check "$use" 'fun
  | .gen k n _ => k + n'
check "$use" 'match h : v with
  | .gen k n _ => k + n'
check "$use" 'if let .gen k _ _ := v then k'
check "$use" '| .gen k n _ => return k + n + x'
check "$use" '| .wrap _ (.gen k _ _) => do'
check "$use" '| .wrap _ (.gen j _ _) => return j + k'
check "$use" '| .mark _ (.gen k _ _) => k'
check "$use" '| .pair (.vec (c@⟨_, _, _⟩)) (.gen k _ _) => k + c.n'
check "$use" 'def genTerm1 : V := .gen 1
'
check "$use" 'def genTerm2 : V := V.gen 1 2
'
check "$use" 'def genMap : List V := [1, 2].map V.gen
'

# A constructor with no default: ellipsis, `@C`, partial application and eta, `cases` alternatives
# and binder-named patterns.  Kv is declared with the new parameter first, as a refactor would.
sed -i 's/^  | pair : Kv → Kv → Kv$/  | pair : Kv → Kv → (s : Bool) → Kv/' Ctor/Kv.lean
"$root/scripts/lean-refactor" insert-arg Ctor.Kv.pair 3 false --in 'Ctor/*.lean' --apply
sed -i 's/^  | tagged : Nat → Nat → {ix : Nat} → Kv$/  | tagged : Nat → Nat → (s : Bool) → {ix : Nat} → Kv/' Ctor/Kv.lean
"$root/scripts/lean-refactor" insert-arg Ctor.Kv.tagged 3 false --in 'Ctor/*.lean' --apply
kv=$(cat Ctor/Kv.lean); kvuse=$(cat Ctor/KvUse.lean)
check "$kv" '.pair k v false'
check "$kv" '| .pair k v _ => .pair v k false'
check "$kvuse" '| @Kv.tagged a b _ _'
check "$kvuse" '| .pair .. => true'
check "$kvuse" '| #[.pair _ (.leaf n) _] => n'
check "$kvuse" 'vs.map ((fun x1 => Kv.pair k x1 false))'
check "$kvuse" ':= (fun x1 => Ctor.Kv.pair k x1 false)'
check "$kvuse" 'List.zipWith (fun x1 x2 => Ctor.Kv.pair x1 x2 false) ks vs'
check "$kvuse" '| .tagged pair _ _ => pair'
check "$kvuse" '(h : ∀ k v, x ≠ .pair k v false)'
check "$kvuse" '| pair k v => trivial'
exit $fail
