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
  imports   : Array String

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

/-- `text` is `prefix` followed by digits, possibly in underscore-separated groups — `match_1`,
    `eq_17`, and the `match_1_1` a splitter gets, which a digits-only test called hand-written and
    let into the duplicate report by the hundred. -/
private def numbered (pre text : String) : Bool :=
  text.startsWith pre &&
    (let rest := text.drop pre.length
     !rest.isEmpty && (rest.toString.splitOn "_").all fun part =>
       !part.isEmpty && part.all Char.isDigit)

/-- The auxiliary shapes a leading underscore actually marks.  `Name.isInternalDetail` calls ANY
    `_`-prefixed component the compiler's own, and this repository writes `_prodPB`, `_idB`,
    `_mfTerm` by hand — 51 of them, every one with a source position.  Called internal, they were
    dropped from the public set while the definitions naming them stayed in it, so the underscore
    alone does not decide this and the shapes do. -/
private def auxiliaryPrefix (s : String) : Bool :=
  ["_aux_", "_proof_", "_private", "_cstage", "_spec", "_redArg", "_lam_", "_flat_ctor",
   "_sizeOf_", "_hyg", "_elabRules", "_simp_", "_regBuiltin", "_closed",
   -- The eliminator Lean derives for a wide match; `_sparseCasesOn_3` is its own component, and it
   -- filled the duplicate report because two parsers matching alike derive the same one.
   "_sparseCasesOn"].any (s.startsWith ·)

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
      -- `_default` is a structure field's default value, which the compiler writes; two fields with
      -- the same default are not a duplicate anyone can act on.
      ["eq_def", "splitter", "inj", "injEq", "noConfusion", "noConfusionType", "sizeOf_spec",
       "casesOn", "recOn", "brecOn", "below", "ibelow", "binductionOn", "ndrec",
       "_default"].contains s

/-! ## Duplicate keys

Two hashes per declaration, each finding a kind of duplicate the other cannot, and neither visible to
the syntax key `dup` reports from `syntax_node`:

* `stmt_key` is the alpha- and universe-normalised STATEMENT.  Equal keys are the same fact however
  it was proved — two independent proofs of one lemma share no source text and no dependency, so
  nothing else here can pair them.
* `skel` is the proof VALUE's structural skeleton: the application tree and the constants it calls,
  with binder names, fvars, literals and universes blanked.  A proof copied and adapted to a weaker
  hypothesis keeps its shape while its statement changes, which is what the statement key misses.

Both are computed from the `.olean` alone, so a repository is scanned without importing it. -/

/-- `mdata` carries source positions and elaborator residue: it hashes as a node of its own and says
    nothing about the statement.  Binder names need no erasing — `Expr.hash` mixes the depth and the
    child hashes at a binder, so it is alpha-invariant already. -/
private partial def stripMData : Expr → Expr
  | .forallE n t b bi => .forallE n (stripMData t) (stripMData b) bi
  | .lam n t b bi     => .lam n (stripMData t) (stripMData b) bi
  | .letE n t v b nd  => .letE n (stripMData t) (stripMData v) (stripMData b) nd
  | .app f a          => .app (stripMData f) (stripMData a)
  | .mdata _ e        => stripMData e
  | .proj s i e       => .proj s i (stripMData e)
  | e                 => e

/-- The binder names of `e`'s leading `∀` telescope.  For a constructor type these are the structure's
    field names, and `Expr.hash` cannot see them: `RelObj.carrier` and `Alg.RelMapObj.obj` are both
    one-field wrappers over `Type u`, and only the field name tells them apart. -/
private partial def binderNames : Expr → List Name
  | .forallE n _ b _ => n :: binderNames b
  | _ => []

/-- `e` with universe parameters renamed positionally, so a lemma over `{u v}` and its copy over
    `{v u}` still compare equal. -/
private def normLevels (levelParams : List Name) (e : Expr) : Expr :=
  e.instantiateLevelParams levelParams
    (levelParams.mapIdx fun i _ => .param (.mkSimple s!"u{i}"))

/-- The statement hash.  Theorems and axioms key on the type alone — proof irrelevance means the same
    statement IS the same fact.  A definition keys on type AND value: many definitions share a type,
    so only an identical body is evidence of a copy.

    An inductive has no value, and its former's type is only its arity — keying on that collided every
    class of equal arity (41 at `(𝒞 : Type u) → [Cat 𝒞] → Type (max u v)`).  It keys on its
    constructors' types instead, with references to its own mutual block replaced by positional
    markers so two structures compare by their fields rather than by their names, and on the
    constructor and field names, without which every pair of equal-arity enumerations merged. -/
private def statementKey (consts : Std.HashMap Name ConstantInfo) (ci : ConstantInfo) : UInt64 :=
  let canon (e : Expr) : UInt64 := (stripMData (normLevels ci.levelParams e)).hash
  match ci with
  | .thmInfo _ | .axiomInfo _ => canon ci.type
  | .inductInfo ind =>
    let deSelf (e : Expr) : Expr := e.replace fun
      | .const n _ => (ind.all.idxOf? n).map fun i => .const (.mkSimple s!"#self{i}") []
      | _ => none
    let ctorKey (h : UInt64) (c : Name) : UInt64 :=
      let ty := deSelf ((consts[c]?).map (·.type) |>.getD default)
      let ctorName := match c with | .str _ s => s | _ => ""
      mixHash (mixHash h (mixHash (hash ctorName) (hash (binderNames ty)))) (canon ty)
    ind.ctors.foldl ctorKey (mixHash (hash ind.numParams) (canon (deSelf ci.type)))
  | _ => mixHash (canon ci.type) ((ci.value?.map canon).getD 0)

/-- The skeleton hash of a proof term, and the number of distinct nodes it has.

    The skeleton is the application tree and the constants the proof CALLS, with everything a copy
    would legitimately change — binder names, fvars, literals, universes — blanked.  Constant heads
    are kept: which lemmas the proof calls, in what shape, is exactly the copy-paste signal.

    Hashed over the DAG rather than over a rebuilt `Expr`.  Building the skeleton as a term first is
    the obvious implementation and it exhausts 30 GB on this repository: a proof term is a DAG whose
    shared subterms are re-expanded into a tree the moment a new `Expr` is constructed.  Memoising
    on the ORIGINAL node's hash keeps the sharing, so the cost is the DAG's size and not the tree's. -/
private partial def skeletonOf (root : Expr) : UInt64 × Nat := Id.run do
  let rec go (e : Expr) : StateM (Std.HashMap UInt64 UInt64) UInt64 := do
    if let some cached := (← get)[e.hash]? then return cached
    let h ← match e with
      | .bvar i           => pure (mixHash 1 (hash i))
      | .fvar _ | .mvar _ => pure (mixHash 1 0)          -- as `.bvar 0`: a copy may rename either
      | .sort _           => pure (mixHash 2 0)
      | .const c _        => pure (mixHash 3 (hash c))
      | .lit _            => pure (mixHash 4 0)
      | .app f a          => pure (mixHash 5 (mixHash (← go f) (← go a)))
      | .lam _ t b bi     => pure (mixHash 6 (mixHash (hash bi.isInstImplicit) (mixHash (← go t) (← go b))))
      | .forallE _ t b bi => pure (mixHash 7 (mixHash (hash bi.isInstImplicit) (mixHash (← go t) (← go b))))
      | .letE _ t v b _   => pure (mixHash 8 (mixHash (← go t) (mixHash (← go v) (← go b))))
      | .mdata _ inner    => go inner
      | .proj st i inner  => pure (mixHash 9 (mixHash (hash st) (mixHash (hash i) (← go inner))))
    modify (·.insert e.hash h)
    return h
  let (h, seen) := go root |>.run ∅
  return (h, seen.size)

/-- The head of a proof after its leading binders, for spotting `rfl`-shaped proofs. -/
private partial def proofHead : Expr → Expr
  | .lam _ _ b _ => proofHead b
  | .mdata _ e   => proofHead e
  | e            => e.getAppFn

/-- The skeleton hash of a declaration's value, and the size that says whether it means anything.
    `none` for a declaration with no value, and for the `rfl`-shaped proofs that otherwise collide by
    the thousand and say nothing. -/
private def skeletonKey (ci : ConstantInfo) : Option (UInt64 × Nat) := do
  let value ← ci.value?
  match proofHead value with
  | .const c _ => if c == ``rfl || c == ``Eq.refl then none else some (skeletonOf value)
  | _ => some (skeletonOf value)

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
  let mut imports := #[]
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
    -- The header the module was compiled with, already in hand: it is what decides whether one
    -- declaration can even SEE another, which no dependency edge answers — `dep` records what a
    -- module used, and a module can see far more than it used.
    for imp in datas[0]!.imports do
      imports := imports.push s!"{toString mod}{fieldSep}{toString imp.module}"
    let consts := moduleConstants datas
    for ci in consts.valuesArray do
      let some kind := kindOf ci | continue
      let name := toString ci.name
      -- De-mangled, because a private copy re-proving a public lemma is a duplicate no name-grep can
      -- see; the de-mangled name is what makes the two comparable, and what says which rows are the
      -- compiler's own (`.eq_1`, `.match_1`, `._simp_1_1`) rather than something anyone wrote.
      let userName := (privateToUserName? ci.name).getD ci.name
      -- The empty `stmt` cell: a signature is the SOURCE's, so the syntax pass fills it in by
      -- position afterwards, and `.import` needs the record as wide as the table meanwhile.
      let (skel, skelSize) := match skeletonKey ci with
        | some (h, n) => (toString (h &&& 0x7fffffffffffffff), toString n)
        | none => ("", "0")
      declInfos := declInfos.push (String.intercalate fieldSep
        [name, toString userName, toString mod, kind,
         if generatedName userName then "1" else "0", "",
         toString (statementKey consts ci &&& 0x7fffffffffffffff), skel, skelSize])
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
  return { declInfos, deps, imports }

end LeanRefactor.OleanRows
