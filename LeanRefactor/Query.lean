module

import Lean
import LeanRefactor.Db
-- The public signature below mentions `Std.HashMap`, which `import Lean` only brings in privately.
public import Std.Data.HashMap.Basic

open Lean

namespace LeanRefactor.Query

/-- One recorded occurrence, in the 0-based LSP coordinates the index stores. -/
public structure Site where
  l1 : Nat
  c1 : Nat
  l2 : Nat
  c2 : Nat

/-- Every USE site (never the binding site) of `declName`, grouped by the source path of the module it
    occurs in — `Freyd/S1_45.lean`, taken from the index's `module.source` column, so the caller can
    match it against the glob's paths directly. -/
public def useSitesByFile (dbPath declName : String) : IO (Std.HashMap String (Array Site)) := do
  -- Single quotes in `declName` are escaped by doubling, as SQL string literals require.
  let sql := s!"select m.source as source, u.l1 as l1, u.c1 as c1, u.l2 as l2, u.c2 as c2
from use_site u join module m on m.name = u.use_module
where u.name = '{declName.replace "'" "''"}' and u.is_definition = 0"
  let j ← Db.query dbPath sql
  let mut map : Std.HashMap String (Array Site) := {}
  match j with
  | .arr rows =>
      -- sqlite3 prints integer columns as JSON numbers; a row whose fields do not parse is skipped.
      for row in rows do
        let source := (row.getObjValAs? String "source").toOption
        let l1 := (row.getObjValAs? Nat "l1").toOption
        let c1 := (row.getObjValAs? Nat "c1").toOption
        let l2 := (row.getObjValAs? Nat "l2").toOption
        let c2 := (row.getObjValAs? Nat "c2").toOption
        match source, l1, c1, l2, c2 with
        | some source, some l1, some c1, some l2, some c2 =>
            map := map.insert source (map.getD source #[] |>.push { l1, c1, l2, c2 })
        | _, _, _, _, _ => pure ()
  | _ => pure ()
  return map

end LeanRefactor.Query
