namespace Fix.Alg

class PowerAllegory (α : Type) where
  powerObj : α → α
  hom : α → α → Type

infixr:10 " ⟶ " => PowerAllegory.hom

abbrev P {α : Type} [PowerAllegory α] (a : α) : α := PowerAllegory.powerObj a

notation "P[" a:min "]" => PowerAllegory.powerObj a

end Fix.Alg
