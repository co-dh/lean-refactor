import Fix.Base

def natArg (n : Nat) : Vec := mk n
def usizeArg (v : Vec) : Nat := take v.count
def bracketed (n : Nat) : Vec := mk <| take n
def body (v : Vec) : Nat := v.count
def field (n : Nat) : Vec := { count := n, name := "x" }
def nested (n : Nat) : USize := twice (take (size (mk n)))
