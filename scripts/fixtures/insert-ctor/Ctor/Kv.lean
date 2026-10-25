namespace Ctor

/-- A constructor with no default to give: every use, pattern or term, must take the new field. -/
inductive Kv
  | leaf : Nat → Kv
  | pair : Kv → Kv → Kv
  | tagged : Nat → Nat → {ix : Nat} → Kv

def Kv.mkPair (k v : Kv) : Kv := .pair k v

-- In the declaring file a pattern of the old arity fails, and hides its right-hand side until edited.
def Kv.swap : Kv → Kv
  | .pair k v => .pair v k
  | x => x

end Ctor
