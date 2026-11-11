/-! The state after the change: `Vec.count` became a `USize`, and nothing that uses it was edited. -/

structure Vec where
  count : USize
  name : String

def mk (n : USize) : Vec := ⟨n, "v"⟩
def take (k : Nat) : Nat := k
def twice (u : USize) : USize := u + u
def usz : USize := 5
