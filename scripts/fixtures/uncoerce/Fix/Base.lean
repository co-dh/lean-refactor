/-! The state after the change: every binder of `Fix/Use.lean` went from `Nat` to `USize`, and the
    conversions written for the old type are still there. -/

structure Vec where
  count : USize

def mk (n : USize) : Vec := ⟨n⟩
def ans (n : USize) : USize := n
def take (k : Nat) : Nat := k
