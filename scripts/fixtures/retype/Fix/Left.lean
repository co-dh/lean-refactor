import Fix.Base

/-! Every site here is one `retype` must leave, and report. -/

structure Old where
  size : Nat

def field : Old := { size := usz }
def notVar (k : Nat) : Vec := mk (take k)
def pat : Option Nat → Vec
  | some n => mk n
  | none => mk 0
def auto (f : Fin n) : Vec := mk n
def other (n : Nat) : Vec := have h : n + 0 = n := Nat.add_zero n; mk n

section
variable (z : Nat)
def z1 : Vec := mk z
def z2 : Nat := take z
end
