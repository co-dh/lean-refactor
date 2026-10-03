import Fix.Base

namespace Fix.Use
open Fix.Alg

variable {α : Type} [PowerAllegory α] (a : α)

-- Qualified as far as the open needs: the source spelling still resolves, so it is kept.
def qualified : α := PowerAllegory.powerObj a

-- `@`-explicit.
def explicit : α := @PowerAllegory.powerObj α _ a

-- Dotted on an instance of the class.
def dotted (inst : PowerAllegory α) : α := inst.powerObj a

-- The other structure's field, dotted and qualified: untouched.
def otherDotted (h : HasPowerObject α) : α := h.powerObj a
def otherQualified (h : HasPowerObject α) : α := HasPowerObject.powerObj h a

end Fix.Use
