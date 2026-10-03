import Fix.Base

namespace Fix.Use
open Fix.Alg PowerAllegory

variable {α : Type} [PowerAllegory α] (f : α → α) (a b : α)

-- Dotted, applied to a compound argument, under brackets that hold only the application.
def dotted : α := (PowerAllegory.powerObj (f a))

-- Opened namespace, an operand of an infix arrow.
def opened : Type := powerObj a ⟶ b

-- `@`-explicit, with the implicit arguments written out.
def explicit : α := @PowerAllegory.powerObj α _ a

-- An argument of another application: its brackets stay for `P $0`, go for `P[$0]`.
def inArg : α := f (powerObj a)

-- Nested: the argument is itself a use.
def nested : α := f (PowerAllegory.powerObj (PowerAllegory.powerObj b))

end Fix.Use
