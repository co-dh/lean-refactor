import Fix.Base

local notation "MK " x => mk (take x)

def underNotation (n : Nat) : Vec := MK n
def unrelated : Nat := "oops"
def plain (n : Nat) : Vec := mk n
def notationArg : Vec := mk SEVEN
