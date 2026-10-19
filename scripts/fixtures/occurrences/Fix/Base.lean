namespace Fix

def cost (tc : Nat → Nat) (n : Nat) : Nat := tc n
def graph (f : Nat → Nat) : Nat := f 0

-- A constant whose name is also a binder name of `call`: `(Q := e)` names the binder, not this.
def Q : Nat := 0
def call (Q : Nat) (P : Nat := 0) : Nat := Q + P
structure Pair where
  Q : Nat
  P : Nat

end Fix
