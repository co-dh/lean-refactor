import Fix.Base
open Shape

def term1 : Shape := Shape.gen 3
def term2 (n : Nat) : List Shape := [gen n, .gen (n + 1)]
def viaMatch : Shape → Nat
  | gen n => n
  | dot => 0
def viaFun : Shape → Shape := fun
  | Shape.gen n => gen (n + 1)
  | s => s
def viaDot (s : Shape) : Nat := match s with
  | .gen k => k
  | _ => 0
def viaIfLet (s : Shape) : Nat := if let gen a := s then a else 0
