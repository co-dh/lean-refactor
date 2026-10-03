namespace Fix.Alg

class PowerAllegory (α : Type) where
  powerObj : α → α
  -- The class's own law names the field as a local bound at the field, not as the constant.
  powerObj_idem : ∀ a, powerObj (powerObj a) = powerObj a

end Fix.Alg

namespace Fix

-- A different field with the same last component: renaming the class field must leave it alone.
structure HasPowerObject (α : Type) where
  powerObj : α → α
  powerObj_idem : ∀ a, powerObj (powerObj a) = powerObj a

end Fix
