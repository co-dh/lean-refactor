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

/-- The `.olean` files of one module under `buildDir`, in the order the module system saves them:
    the main part, then the server and private parts when the module is split. -/
private def oleanParts (buildDir : String) (mod : Name) : Array System.FilePath :=
  let base := System.FilePath.mk (buildDir ++ "/" ++ (toString mod).replace "." "/")
  #[base.addExtension "olean", base.addExtension "olean.server", base.addExtension "olean.private"]

/-- The constants of one module from its parts, one entry per name. The parts overlap: the private
    part holds every constant, the exported and server parts the exported subset, with definitions
    weakened to axioms. The private part comes last, so the last occurrence wins and the weakened
    forms are discarded. -/
private def moduleConstants (datas : Array ModuleData) : Array ConstantInfo :=
  let byName : Std.HashMap Name ConstantInfo := {}
  (datas.foldl (fun m data => data.constants.foldl (fun m ci => m.insert ci.name ci) m) byName).valuesArray

/-- Read each module's `.olean` under `buildDir` — no environment, no imports, no search path — and produce its
    rows. A module whose `.olean` is missing or unreadable is skipped, not an error. -/
public def ofModules (modules : Array Name) (buildDir : String := ".lake/build/lib/lean") : IO Rows := do
  let mut declInfos := #[]
  let mut deps := #[]
  for mod in modules do
    let parts ← (oleanParts buildDir mod).filterM fun p => do System.FilePath.pathExists p
    if parts.isEmpty then continue
    -- A split module's parts share compacted data, so they must be read together; if that fails, the
    -- main part alone still holds every constant.
    let datas ←
      if parts.size == 1 then
        let part ← readModuleData parts[0]!
        pure #[part.1]
      else
        try
          let mdps ← readModuleDataParts parts
          pure (mdps.map (·.1))
        catch _ =>
          let part ← readModuleData parts[0]!
          pure #[part.1]
    for ci in moduleConstants datas do
      let some kind := kindOf ci | continue
      let name := toString ci.name
      declInfos := declInfos.push s!"{name}{fieldSep}{toString mod}{fieldSep}{kind}{fieldSep}{typeKey ci.type}"
      let used := (ci.type.getUsedConstants ++ (ci.value?.map (·.getUsedConstants)).getD #[]).toList.eraseDups
      for dst in used do
        if dst == ci.name then continue
        deps := deps.push s!"{name}{fieldSep}{toString dst}{fieldSep}{toString mod}"
  return { declInfos, deps }

end LeanRefactor.OleanRows
