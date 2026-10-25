namespace Ctor

inductive Enc where
  | raw (n : Nat)
  | packed (a b : Nat)

structure Col where
  ty : Nat
  n : Nat
  enc : Enc

def inFile : Col := ⟨0, 1, .raw 2⟩

inductive V where
  | vec (k : Nat) (n : Nat) (a : Option Nat)
  | atom (x : Nat)

-- `test-insert-ctor.sh` gives `gen` a third parameter WITH a default, as qlean's `QValue.general` got one.
@[match_pattern] abbrev V.gen (k : Nat) (n : Nat := 0) : V := .vec k n none

end Ctor
