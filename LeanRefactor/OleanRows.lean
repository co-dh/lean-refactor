module

import Lean

open Lean

namespace LeanRefactor.OleanRows

/-- 0x1F, matching sqlite3's `--ascii` import mode. Kept in step with `LeanRefactor.Db.fieldSep`. -/
private def fieldSep : String := "\x1f"

/-- The rows a set of compiled modules produces. Each string is one record: the cell values joined by
    `LeanRefactor.Db.fieldSep`. -/
public structure Rows where
  declInfos : Array String
  deps      : Array String

/-- Kind string for a constant, or `none` for constructors, recursors and quotients, which belong to
    their inductive and get no row of their own. -/
private def kindOf (ci : ConstantInfo) : Option String :=
  match ci with
  | .thmInfo _    => some "thm"
  | .defnInfo _   => some "def"
  | .axiomInfo _  => some "axiom"
  | .inductInfo _ => some "ind"
  | .opaqueInfo _ => some "opaque"
  | .ctorInfo _   => none
  | .recInfo _    => none
  | .quotInfo _   => none

/-- Statement hash as a string. The mask keeps the value below 2^63: SQLite integers are signed 64-bit,
    and an unmasked `UInt64` at or above 2^63 does not survive the import as an integer. -/
private def typeKey (e : Expr) : String :=
  toString (e.hash &&& 0x7fffffffffffffff)

/-- Import `modules` — ONE environment, in this one process — and produce rows for exactly those modules.
    Modules that are not found in the environment header are skipped, not an error. -/
public def ofModules (modules : Array Name) : IO Rows := do
  initSearchPath (← findSysroot)
  -- `importModules` throws on a module whose `.olean` is not in the search path; drop those first.
  let modules ← modules.filterM fun n => do
    try
      _ ← findOLean n
      pure true
    catch _ =>
      pure false
  let env ← importModules (modules.map fun n => { module := n, importAll := true }) {}
  let names := env.header.moduleNames
  let data := env.header.moduleData
  let mut declInfos := #[]
  let mut deps := #[]
  for mod in modules do
    let some idx := names.idxOf? mod | continue
    for ci in data[idx]!.constants do
      let some kind := kindOf ci | continue
      let name := toString ci.name
      declInfos := declInfos.push s!"{name}{fieldSep}{toString mod}{fieldSep}{kind}{fieldSep}{typeKey ci.type}"
      let used := (ci.type.getUsedConstants ++ (ci.value?.map (·.getUsedConstants)).getD #[]).toList.eraseDups
      for dst in used do
        if dst == ci.name then continue
        deps := deps.push s!"{name}{fieldSep}{toString dst}{fieldSep}{toString mod}"
  return { declInfos, deps }

end LeanRefactor.OleanRows
