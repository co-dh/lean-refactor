import Fix.Base

namespace Fix.Use
open Fix.Ops

def arrow (a : Nat) : Except String Nat := do
  let x ← step a 1
  pure x

def qualified (a : Nat) : Except String Nat := do
  let x ← Fix.Ops.step a 2
  return x

def lifted (a : Nat) : Except String Nat := do
  return (← step a 3) + 1

def explicit (a : Nat) : Except String Nat := do
  let x ← @step a 4
  pure x

def named (a : Nat) : Except String Nat := do
  let x ← step (b := 5) (a := a)
  pure x

def multiline (a : Nat) : Except String Nat := do
  let x ← step
    a
    6
  pure x

def reassign (a : Nat) : Except String Nat := do
  let mut x := a
  x ← step x 7
  pure x

def letOk (a : Nat) : Except String Nat := do
  let .ok r := step a 8 | throw "no"
  pure r

def letSome (k : Nat) : Nat := Id.run do
  let some r := look k | 0
  return r

def letSomeQualified (k : Nat) : Nat := Id.run do
  let Option.some r := look k
    | 0
  return r

def dotted (b : Box) : Except String Nat := do
  let x ← b.get 1
  pure x

def piped (b : Box) : Except String Nat := do
  let x ← b |>.get 2
  pure x

theorem eqDot (a : Nat) : step a 0 = .ok a := rfl

theorem eqQualified (a : Nat) (h : step a 1 = Except.ok (a + 1)) : True := trivial

theorem eqPure (a : Nat) : step a 2 = pure (a + 2) := rfl

theorem eqSome (k : Nat) : look k = some k := rfl

theorem eqFlipped (k : Nat) : some k = look k := rfl

theorem eqBox (b : Box) : (b.get 3) = .ok (b.n + 3) := rfl

def unknownMatch (a : Nat) : Nat :=
  match step a 9 with
  | .ok r => r
  | .error _ => 0

theorem gateDrops (a : Nat) (h : step a 11 = .ok 0) : a + 11 = 0 := Except.ok.inj h

def matchSome (k : Nat) : Nat :=
  match look k with
  | none => 0
  | some r => r + 1

def body (a : Nat) : Except String Nat := step a 13

def doLast (a : Nat) : Except String Nat := do
  let y := a
  step y 14

def altRhs (a : Nat) (b : Bool) : Except String Nat :=
  match b with
  | true => step a 15
  | false => .ok a

def branch (a : Nat) (b : Bool) : Except String Nat :=
  if b then step a 16 else .ok a

def lam : Nat → Except String Nat := fun a => step a 17

def arg (a : Nat) : Except String Nat := Except.map id (step a 18)

structure Pair where
  v : Except String Nat

def field (a : Nat) : Pair := { v := step a 19 }

def optBody (k : Nat) : Option Nat := look (k + 1)

def proj (a : Nat) : Bool := (step a 12).toBool

theorem mention : True := by simp [step]

end Fix.Use
