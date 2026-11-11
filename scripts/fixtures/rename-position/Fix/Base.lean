/-! `Shape.gen` is used both as a term and, being `@[match_pattern]`, as a pattern. -/

inductive Shape where
  | box (n : Nat)
  | dot

namespace Shape
@[match_pattern] def gen (n : Nat) : Shape := box n
end Shape
