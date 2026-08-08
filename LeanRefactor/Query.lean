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

/-- Single quotes in `declName` are escaped by doubling, as SQL string literals require. -/
private def escaped (declName : String) : String :=
  declName.replace "'" "''"

/-- Every USE site (never the binding site) of `declName`, grouped by the source path of the module it
    occurs in — `Freyd/S1_45.lean`, taken from the index's `module.source` column, so the caller can
    match it against the glob's paths directly. -/
public def useSitesByFile (dbPath declName : String) : IO (Std.HashMap String (Array Site)) := do
  let sql := s!"select m.source as source, u.l1 as l1, u.c1 as c1, u.l2 as l2, u.c2 as c2
from use_site u join module m on m.name = u.use_module
where u.name = '{escaped declName}' and u.is_definition = 0"
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

/-- The module names a `select distinct module as m` query returned, in row order. -/
private def namedModules (j : Json) : Array String :=
  match j with
  | .arr rows => rows.filterMap fun row => (row.getObjValAs? String "m").toOption
  | _ => #[]

/-- Modules with at least one recorded USE site of `declName`, each with its site count, name-sorted. -/
public def useModules (dbPath declName : String) : IO (Array (String × Nat)) := do
  let j ← Db.query dbPath s!"select use_module as m, count(*) as n from use_site
where name = '{escaped declName}' and is_definition = 0 group by use_module order by use_module"
  match j with
  | .arr rows =>
      -- sqlite3 prints integer columns as JSON numbers; a row whose fields do not parse is skipped.
      let mut out := #[]
      for row in rows do
        let m := (row.getObjValAs? String "m").toOption
        let n := (row.getObjValAs? Nat "n").toOption
        match m, n with
        | some m, some n => out := out.push (m, n)
        | _, _ => pure ()
      return out
  | _ => return #[]

/-- Modules whose declarations mention `declName` in a type or a proof term, name-sorted. -/
public def dependentModules (dbPath declName : String) : IO (Array String) := do
  let j ← Db.query dbPath s!"select distinct module as m from dep where dst = '{escaped declName}' order by module"
  return (namedModules j)

/-- Modules that depend on `declName` without naming it anywhere the info trees recorded: they reach it
    through notation or macro expansion.  No edit is needed there — the notation is declared once — but
    they are exactly the modules a rename can break without touching. -/
public def silentDependents (dbPath declName : String) : IO (Array String) := do
  let j ← Db.query dbPath s!"select distinct module as m from dep where dst = '{escaped declName}'
except select distinct use_module from use_site where name = '{escaped declName}' and is_definition = 0
order by 1"
  return (namedModules j)

/-- The `module.source` path of every module, keyed by its `module.name` — the join the path-facing
    callers need when a query returns module names. -/
public def moduleSources (dbPath : String) : IO (Std.HashMap String String) := do
  let j ← Db.query dbPath "select name, source from module"
  let mut map : Std.HashMap String String := {}
  match j with
  | .arr rows =>
      for row in rows do
        let name := (row.getObjValAs? String "name").toOption
        let source := (row.getObjValAs? String "source").toOption
        match name, source with
        | some name, some source => map := map.insert name source
        | _, _ => pure ()
  | _ => pure ()
  return map

end LeanRefactor.Query
