import Fix.Base

namespace Fix

def Qc : Nat := 3

-- remove-arg Fix.cost 1: only applications whose HEAD is the constant `Fix.cost` lose an argument.
def ascribed (tc : Nat → Nat) : Nat := (graph (cost tc) : Nat)
def full (tc : Nat → Nat) : Nat := cost tc 5
def nested (h : (Nat → Nat) → Nat) : Nat := h (cost id)
def localSameName : ((Nat → Nat) → Nat → Nat) → Nat := fun cost => cost id 1
def boundSameName (cost : (Nat → Nat) → Nat → Nat) : Nat := cost id 2
def unapplied (h : ((Nat → Nat) → Nat → Nat) → Nat) : Nat := h cost

-- rename Fix.Q Fix.Qbook: a named argument's NAME is the callee's binder, its VALUE is a term.
def named : Nat := call (Q := Qc)
def namedValue : Nat := call (P := Q) (Q := Qc)
def namedExplicit : Nat := @call (Q := Q) (P := 1)
def fields : Pair := { Q := Q, P := 1 }
def letSameName : Nat := let Q := 4; Q + Fix.Q

end Fix
