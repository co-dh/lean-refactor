import Ctor.Kv

namespace Ctor

def kvExplicit : Kv → Nat
  | @Kv.tagged a b _ => a + b
  | _ => 0

def kvEllipsis : Kv → Bool
  | .pair .. => true
  | _ => false

def kvMatches (x : Kv) : Bool := x matches .pair ..

def kvArray : Array Kv → Nat
  | #[.pair _ (.leaf n)] => n
  | _ => 0

def kvPartial (k : Kv) (vs : List Kv) : List Kv := vs.map (Kv.pair k)

def kvPartialDot (k : Kv) : Kv → Kv := .pair k

def kvUnapplied (ks vs : List Kv) : List Kv := List.zipWith Kv.pair ks vs

def kvVar : Kv → Nat
  | .tagged pair _ => pair
  | _ => 0

theorem kvCases (x : Kv) (h : ∀ k v, x ≠ .pair k v) : True := by
  cases x with
  | pair k v => trivial
  | _ => trivial

end Ctor
