import Fix.Base

local notation "TOU " x => Nat.toUSize x

def dotted (n : USize) : Vec := mk n.toUSize
def spelled (n : USize) : Vec := mk (Nat.toUSize n)
def expected (n : USize) : USize := ans n.toNat
def body (n : USize) : USize := n.toNat
def paren (n : USize) : USize := ans (n.toNat)
def arith (a b : USize) : USize := ans (Nat.toUSize (a + b))
def chain (n : USize) : USize := ans (n.toUSize).toNat
def trip (n : USize) : USize := ans n.toNat.toUSize
def lossy (n : Nat) : Nat := take (Nat.toUSize n).toNat
def still (n : USize) : Nat := take n.toUSize
def viaNotation (n : USize) : Vec := mk (TOU n)
def unrelated : Nat := "oops"
