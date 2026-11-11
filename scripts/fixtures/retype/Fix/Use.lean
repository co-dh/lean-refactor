import Fix.Base

/-! Every site here is fixed by a retype, or by `--convert` on a retyped binder's use as a `Nat`. -/

def single (n : Nat) : Vec := mk n
def group (n m : Nat) : Vec := { count := n, name := toString m }
def caller (k : Nat) : Vec := single k
def needs (n : Nat) : Vec × Nat := (mk n, take n)
def body (v : Vec) : Nat := v.count
def lam : Vec := (fun (n : Nat) => mk n) 3
def letb : Vec := let n : Nat := 3; mk n
theorem ex : ∃ n : Nat, (mk n).name = "v" := ⟨0, rfl⟩

section
variable (w : Nat)
def v1 : Vec := mk w
def v2 : USize := twice w
end
