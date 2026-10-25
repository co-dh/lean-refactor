namespace Ctor

inductive Enc where
  | raw (n : Nat)
  | packed (a b : Nat)

structure Col where
  ty : Nat
  n : Nat
  enc : Enc

def inFile : Col := ⟨0, 1, .raw 2⟩

end Ctor
