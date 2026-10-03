import Fix.Base

namespace Fix.Short
open Fix.Alg PowerAllegory

variable {α : Type} [PowerAllegory α] (a : α)

-- Through `open … PowerAllegory`: the shortest spelling that resolves to the new constant.
def opened : α := powerObj a

-- Fully qualified in the source: still resolves, so kept.
def full : α := Fix.Alg.PowerAllegory.powerObj a

end Fix.Short
