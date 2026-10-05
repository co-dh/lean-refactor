import Lean
import Fix.Base

namespace Fix.Use
open Lean

@[app_unexpander Fix.Alg.RelSet.Edit.leqN] def unexpLeqN : PrettyPrinter.Unexpander
  | _ => throw ()

open Fix.Alg.RelSet

attribute [local simp] Edit.leqN

example : Edit.leqN 1 1 := Nat.le_refl 1

end Fix.Use
