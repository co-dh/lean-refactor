module

import Lean

open Lean Lean.Server

namespace LeanRefactor.IleanRows

/-- 0x1F, matching sqlite3's `--ascii` import mode. Kept in step with `LeanRefactor.Db.fieldSep`. -/
private def fieldSep : String := "\x1f"

/-- The rows one module's `.ilean` produces. Each string is one record: the cell values joined by
    `LeanRefactor.Db.fieldSep`. -/
public structure Rows where
  declRanges : Array String
  useSites   : Array String

/-- One `use_site` record: the constant's name and DEFINING module, the module owning the
    occurrence, the location, the enclosing declaration, and whether the site is the binding
    site rather than a use.  The distinction is the operation: `rename` moves uses only,
    `rename-decl` moves the binding site too. -/
private def useSiteRow (name declModule module : String) (loc : Lsp.RefInfo.Location)
    (isDefinition : Bool) : String :=
  String.intercalate fieldSep #[name, declModule, module, toString loc.startPosLine,
    toString loc.startPosCharacter, toString loc.endPosLine, toString loc.endPosCharacter,
    loc.parentDecl, if isDefinition then "1" else "0"].toList

/-- Load `ileanPath` and produce that module's rows. -/
public def ofIlean (ileanPath : System.FilePath) : IO Rows := do
  let ilean ← Ilean.load ileanPath
  let module := ilean.module.toString
  let declRanges : Array String := Id.run do
    let mut rows := #[]
    for (name, d) in ilean.decls do
      rows := rows.push <| String.intercalate fieldSep #[name, module,
        toString d.rangeStartPosLine, toString d.rangeStartPosCharacter,
        toString d.rangeEndPosLine, toString d.rangeEndPosCharacter,
        toString d.selectionRangeStartPosLine, toString d.selectionRangeStartPosCharacter,
        toString d.selectionRangeEndPosLine, toString d.selectionRangeEndPosCharacter].toList
    rows
  let useSites : Array String := Id.run do
    let mut rows := #[]
    for (ident, info) in ilean.references do
      match ident with
      | .fvar _ _ => pure ()  -- locals are filtered out of `.ilean`; there is nothing to record
      | .const declModule name =>
          if let some loc := info.definition? then
            rows := rows.push (useSiteRow name declModule module loc true)
          for loc in info.usages do
            rows := rows.push (useSiteRow name declModule module loc false)
    rows
  pure { declRanges, useSites }

end LeanRefactor.IleanRows
