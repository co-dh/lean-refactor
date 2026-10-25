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

def genBoth : V → Nat
  | .gen k n => k + n
  | _ => 0

def genShort : V → Nat
  | .gen k => k
  | _ => 0

-- Every place a pattern can stand, each spelling `.gen` with both explicit arguments.
def genNested : V → Nat
  | .wrap _ (.gen k n) => k + n
  | _ => 0

def genAs : V → Nat
  | .wrap _ (v@(.gen _ _)) => genBoth v
  | _ => 0

def genAlts : Nat → V → Nat
  | _, .atom k | _, .wrap _ (.gen k _) => k
  | _, _ => 0

def genDoBind (v : V) : Id Nat := do
  match v, ← pure 1 with
  | .gen k n, _ => return k + n
  | _, m => return m

def genInnerMatch : Nat → V → Nat
  | 0, _ => 0
  | f + 1, v =>
    let t := f
    match v with
    | .gen k n => k + n + t
    | .wrap _ w => match w with
      | .gen k _ => k
      | _ => 1
    | _ => 0

def genFunAlts : V → Nat := fun
  | .gen k n => k + n
  | _ => 0

def genMatchH (v : V) : Nat :=
  match h : v with
  | .gen k n => k + n
  | _ => 0

def genIfLet (v : V) : Nat := if let .gen k _ := v then k else 0

def genDoMatch (v : V) : Id Nat := do
  let x := 1
  match v with
  | .gen k n => return k + n + x
  | .wrap _ (.gen k _) => do
    match v with
    | .wrap _ (.gen j _) => return j + k
    | _ => return 0
  | _ => return 0

def genMark : V → Nat
  | .mark _ (.gen k _) => k
  | _ => 0

def genPair : V → Nat
  | .pair (.vec (c@⟨_, _, _⟩)) (.gen k _) => k + c.n
  | _ => 0

def genTerm1 : V := .gen 1
def genTerm2 : V := V.gen 1 2
def genMap : List V := [1, 2].map V.gen

end Ctor
