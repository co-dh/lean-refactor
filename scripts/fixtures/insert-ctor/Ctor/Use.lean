import Ctor.Base

namespace Ctor

def anonTerm (t : Nat) : Col := ⟨t, 2, .raw 3⟩
def nested : Option Col := some ⟨1, 2, .packed 3 4⟩
def explicitMk : Col := Col.mk 1 2 (.raw 0)
def dotMk : Col := .mk 1 2 (.raw 0)
def instance' : Col := { ty := 1, n := 2, enc := .raw 0 }
def update (c : Col) : Col := { c with n := 5 }

def matchAnon : Col → Nat
  | ⟨_, _, .packed a b⟩ => a + b
  | ⟨t, _, .raw m⟩ => t + m

def matchMk (c : Col) : Nat :=
  match c with
  | .mk t n _ => t + n

def funPat : Col → Nat := fun ⟨t, _, _⟩ => t
def letPat (c : Col) : Nat := let ⟨_, n, _⟩ := c; n
def ifLet (c : Col) : Nat := if let ⟨t, _, .raw _⟩ := c then t else 0
def doPat (cs : List Col) : Id Nat := do
  let mut s := 0
  for ⟨t, _, _⟩ in cs do s := s + t
  return s

theorem obtained (c : Col) : c.ty = c.ty := by
  obtain ⟨t, n, e⟩ := c
  rfl

theorem anonInStatement : (⟨1, 2, .raw 0⟩ : Col).n = 2 := rfl

end Ctor
