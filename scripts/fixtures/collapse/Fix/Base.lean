namespace Fix.Alg.RelSet

def leRel (a b : Nat) : Prop := a ≤ b

namespace Edit

/-- The duplicate `collapse` removes. -/
def leqN (a b : Nat) : Prop := a ≤ b

theorem leqN_refl (a : Nat) : leqN a a := Nat.le_refl a

end Edit
end Fix.Alg.RelSet
