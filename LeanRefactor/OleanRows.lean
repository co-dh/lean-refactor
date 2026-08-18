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

/-- `text` is `prefix` followed by at least one digit and nothing else — `match_1`, `eq_17`. -/
private def numbered (pre text : String) : Bool :=
  text.startsWith pre &&
    (let rest := text.drop pre.length; !rest.isEmpty && rest.all Char.isDigit)

/-- The auxiliary shapes a leading underscore actually marks.  `Name.isInternalDetail` calls ANY
    `_`-prefixed component the compiler's own, and this repository writes `_prodPB`, `_idB`,
    `_mfTerm` by hand — 51 of them, every one with a source position.  Called internal, they were
    dropped from the public set while the definitions naming them stayed in it, so the underscore
    alone does not decide this and the shapes do. -/
private def auxiliaryPrefix (s : String) : Bool :=
  ["_aux_", "_proof_", "_private", "_cstage", "_spec", "_redArg", "_lam_", "_flat_ctor",
   "_sizeOf_", "_hyg", "_elabRules", "_simp_", "_regBuiltin", "_closed"].any (s.startsWith ·)

/-- Names the compiler wrote, not a person: equation lemmas, match auxiliaries, the `injEq`/
    `noConfusion`/recursor family. `isInternalDetail` alone leaves `match_1.splitter` and `eq_3`
    behind, and those group by the dozen across every module that uses the same definition — noise
    that would open every duplicate report. Recorded once here as a column, so no reader has to
    reinvent the filter as a pattern match on names. -/
private def generatedName (n : Name) : Bool :=
  n.components.any fun component =>
    let s := toString component
    auxiliaryPrefix s ||
    numbered "match_" s || numbered "proof_" s || numbered "eq_" s ||
      -- No `mk`: a real constructor never reaches here, `kindOf` having dropped it, so the only
      -- names the component matched were hand-written `def mk`s — and hiding one of those from
      -- `modularize` left `Freyd.UF.Ultraproduct.mk` unmarked while the `sound` that names it was
      -- public. The `X.mk.injEq` family is already caught by its own last component.
      ["eq_def", "splitter", "inj", "injEq", "noConfusion", "noConfusionType", "sizeOf_spec",
       "casesOn", "recOn", "brecOn", "below", "ibelow", "binductionOn", "ndrec"].contains s

/-- The `.olean` files of one module under `buildDir`, in the order the module system saves them:
    the main part, then the server and private parts when the module is split. -/
private def oleanParts (buildDir : String) (mod : Name) : Array System.FilePath :=
  let base := System.FilePath.mk (buildDir ++ "/" ++ (toString mod).replace "." "/")
  #[base.addExtension "olean", base.addExtension "olean.server", base.addExtension "olean.private"]

/-- The constants of one module from its parts, one entry per name. The parts overlap: the private
    part holds every constant, the exported and server parts the exported subset, with definitions
    weakened to axioms. The private part comes last, so the last occurrence wins and the weakened
    forms are discarded. Returned as the map, not just its values: an inductive's dep edges need its
    constructors' types, and they must come from this same merged view or a split module would take
    them from the weakened forms and disagree with an unsplit one. -/
private def moduleConstants (datas : Array ModuleData) : Std.HashMap Name ConstantInfo :=
  let byName : Std.HashMap Name ConstantInfo := {}
  datas.foldl (fun m data => data.constants.foldl (fun m ci => m.insert ci.name ci) m) byName

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
    let consts := moduleConstants datas
    for ci in consts.valuesArray do
      let some kind := kindOf ci | continue
      let name := toString ci.name
      -- De-mangled, because a private copy re-proving a public lemma is a duplicate no name-grep can
      -- see; the de-mangled name is what makes the two comparable, and what says which rows are the
      -- compiler's own (`.eq_1`, `.match_1`, `._simp_1_1`) rather than something anyone wrote.
      let userName := (privateToUserName? ci.name).getD ci.name
      -- The empty sixth cell is `stmt`: a signature is the SOURCE's, so the syntax pass fills it in
      -- by position afterwards, and `.import` needs the record as wide as the table meanwhile.
      declInfos := declInfos.push (String.intercalate fieldSep
        [name, toString userName, toString mod, kind,
         if generatedName userName then "1" else "0", ""])
      -- An inductive publishes its constructors' types: `structure LawfulPMC` names `pmcCone` in a
      -- field, and `pmcCone` has to be public for the structure to be.  A constructor gets no row of
      -- its own (`kindOf` drops it), and the inductive's own type is only its arity, so without this
      -- the field types are in no dep edge at all and the closure walked straight past them.
      let ctorTypes := match ci with
        | .inductInfo v => v.ctors.foldl (init := #[]) fun acc c =>
            match consts[c]? with
              | some ctor => acc ++ ctor.type.getUsedConstants
              | none => acc
        | _ => #[]
      -- WHERE a constant is named decides what has to be done about it, so the two faces are kept
      -- apart.  A private constant in a public STATEMENT is illegal while the same constant in the
      -- proof is fine; and a definition the code generator compiles must reduce its type the same
      -- way on both sides of a module boundary, which is a demand on the constants in the TYPE and
      -- on no others.  An inductive's constructor types are part of its type face: they are what a
      -- structure publishes.
      let inType := (ci.type.getUsedConstants ++ ctorTypes).toList.eraseDups
      let inValue := ((ci.value?.map (·.getUsedConstants)).getD #[]).toList.eraseDups
      for dst in (inType ++ inValue).eraseDups do
        if dst == ci.name then continue
        deps := deps.push s!"{name}{fieldSep}{toString dst}{fieldSep}{toString mod}\
          {fieldSep}{if inType.contains dst then "1" else "0"}\
          {fieldSep}{if inValue.contains dst then "1" else "0"}"
  return { declInfos, deps }

end LeanRefactor.OleanRows
