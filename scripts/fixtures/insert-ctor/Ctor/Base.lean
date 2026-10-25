namespace Ctor

inductive Enc where
  | raw (n : Nat)
  | packed (a b : Nat)

structure Col where
  ty : Nat
  n : Nat
  enc : Enc

def inFile : Col := ⟨0, 1, .raw 2⟩

mutual
inductive V where
  | vec (c : VC)
  | atom (x : Nat)
  | wrap (t : Nat) (v : V)
  | mark (t : Nat) (v : V) {ix : Nat}
  | pair (a b : V)

structure VC where
  n : Nat
  p : P
  a : Option Nat

inductive P where
  | pay (k : Nat)
  | vs (xs : Array V)
end

-- `test-insert-ctor.sh` gives `gen` a third parameter WITH a default, as qlean's `QValue.general` got one.
-- Shaped as that one is: an abbreviation for a constructor of a mutual block applied to a structure.
@[match_pattern] abbrev V.gen (k : Nat) (n : Nat := 0) : V := .vec ⟨n, .pay k, none⟩

end Ctor
