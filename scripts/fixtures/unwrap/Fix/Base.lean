namespace Fix.Ops

def step (a b : Nat) : Except String Nat := .ok (a + b)

def look (k : Nat) : Option Nat := some k

structure Box where
  n : Nat

def Box.get (b : Box) (k : Nat) : Except String Nat := .ok (b.n + k)

end Fix.Ops
