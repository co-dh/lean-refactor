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

/-- The mask keeps a hash below 2^63: SQLite integers are signed 64-bit, and an unmasked `UInt64` at
    or above 2^63 does not survive the import as an integer. -/
private def cell (h : UInt64) : String :=
  toString (h &&& 0x7fffffffffffffff)

/-- `text` is `prefix` followed by at least one digit and nothing else — `match_1`, `eq_17`. -/
private def numbered (pre text : String) : Bool :=
  text.startsWith pre &&
    (let rest := text.drop pre.length; !rest.isEmpty && rest.all Char.isDigit)

/-- Names the compiler wrote, not a person: equation lemmas, match auxiliaries, the `injEq`/
    `noConfusion`/recursor family. `isInternalDetail` alone leaves `match_1.splitter` and `eq_3`
    behind, and those group by the dozen across every module that uses the same definition — noise
    that would open every duplicate report. Recorded once here as a column, so no reader has to
    reinvent the filter as a pattern match on names. -/
private def generatedName (n : Name) : Bool :=
  n.isInternalDetail || n.components.any fun component =>
    let s := toString component
    numbered "match_" s || numbered "proof_" s || numbered "eq_" s ||
      -- No `mk`: a real constructor never reaches here, `kindOf` having dropped it, so the only
      -- names the component matched were hand-written `def mk`s — and hiding one of those from
      -- `modularize` left `Freyd.UF.Ultraproduct.mk` unmarked while the `sound` that names it was
      -- public. The `X.mk.injEq` family is already caught by its own last component.
      ["eq_def", "splitter", "inj", "injEq", "noConfusion", "noConfusionType", "sizeOf_spec",
       "casesOn", "recOn", "brecOn", "below", "ibelow", "binductionOn", "ndrec"].contains s

/-- Drop `mdata` (source positions and elaborator residue): it hashes as a node of its own but says
    nothing about the statement. -/
private partial def stripMData : Expr → Expr
  | .forallE n t b bi => .forallE n (stripMData t) (stripMData b) bi
  | .lam n t b bi     => .lam n (stripMData t) (stripMData b) bi
  | .letE n t v b nd  => .letE n (stripMData t) (stripMData v) (stripMData b) nd
  | .app f a          => .app (stripMData f) (stripMData a)
  | .mdata _ e        => stripMData e
  | .proj s i e       => .proj s i (stripMData e)
  | e                 => e

/-- `e` with universe parameters renamed to positional `u0, u1, …`, so a lemma generalised over
    `{u v}` and its copy over `{z w}` hash alike. -/
private def normLevels (levelParams : List Name) (e : Expr) : Expr :=
  e.instantiateLevelParams levelParams (levelParams.mapIdx fun i _ => .param (.mkSimple s!"u{i}"))

/-- The binder names of `e`'s leading `∀` telescope. For a constructor type these are the structure's
    field names, and `Expr.hash` cannot see them: `RelObj.carrier` and `Alg.RelMapObj.obj` are both
    one-field wrappers over `Type u`, and only the field name tells them apart. -/
private partial def binderNames : Expr → List Name
  | .forallE n _ b _ => n :: binderNames b
  | _ => []

/-- Statement hash: two declarations with the same key state the same thing.

    Theorems and axioms key on the type alone — proof irrelevance means the same statement is the
    same fact however it was proved. Definitions key on type AND value: a shared type is weak
    evidence for a `def` (many share one), an identical body is a copy-paste.

    An inductive has no value, and its *former's* type says nothing about its fields — keying on
    that collides every class of the same arity. Key on the constructor types instead, with
    references to the mutual block replaced by positional markers so two structures are compared by
    their fields rather than separated by their own names, and on the constructor and field names
    too, which no `Expr` hash sees. Ported from the book repository's `scripts/ExtractGraph.lean`,
    whose keys this must keep reproducing. -/
private def declKey (consts : Std.HashMap Name ConstantInfo) (ci : ConstantInfo) : UInt64 :=
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

/-- Structural skeleton of a proof term: keep the application tree and the CALLED CONSTANTS, blank
    fvars/mvars, sorts, universes and literals. Same skeleton across two declarations = the same
    proof, whatever the statements say — which is the one duplication signal every type-keyed pass
    misses, because a copy-pasted-then-adapted proof has a different type.

    Memoised on the input node so the result keeps the input's sharing. Rebuilding a proof term
    structurally would un-share its DAG and re-walk every shared subterm, which is exponential on
    real proof values; the index runs on every rename, so it must stay linear. -/
private partial def skeleton (e : Expr) : StateM (Std.HashMap Expr Expr) Expr := do
  if let some cached := (← get)[e]? then return cached
  let out ← match e with
    | .fvar _ | .mvar _ => pure (.bvar 0)
    | .sort _           => pure (.sort .zero)
    | .const c _        => pure (.const c [])
    | .lit _            => pure (.lit (.natVal 0))
    | .app f a          => pure (.app (← skeleton f) (← skeleton a))
    | .lam _ t b bi     => pure (.lam `_ (← skeleton t) (← skeleton b) bi)
    | .forallE _ t b bi => pure (.forallE `_ (← skeleton t) (← skeleton b) bi)
    | .letE _ t v b nd  => pure (.letE `_ (← skeleton t) (← skeleton v) (← skeleton b) nd)
    | .mdata _ e        => skeleton e
    | .proj s i e       => pure (.proj s i (← skeleton e))
    | e                 => pure e
  modify (·.insert e out)
  return out

/-- The number of DISTINCT nodes in a skeleton's DAG. Tiny proofs collide en masse and say nothing,
    so this is what a report thresholds on. Nodes already seen are skipped, which keeps the walk
    linear in the DAG rather than in the tree it unfolds to. -/
private partial def skeletonNodes (e : Expr) : Nat :=
  let rec go (e : Expr) : StateM (Std.HashSet UInt64) Unit := do
    if (← get).contains e.hash then return
    modify (·.insert e.hash)
    match e with
    | .app f a         => go f; go a
    | .lam _ t b _     => go t; go b
    | .forallE _ t b _ => go t; go b
    | .letE _ t v b _  => go t; go v; go b
    | .mdata _ e       => go e
    | .proj _ _ e      => go e
    | _                => pure ()
  ((go e).run {}).2.size

/-- Head of a proof after stripping leading binders and `mdata`, to spot `rfl`-shaped proofs. -/
private partial def proofHead : Expr → Expr
  | .lam _ _ b _ => proofHead b
  | .mdata _ e   => proofHead e
  | e            => e.getAppFn

/-- The proof key and its node count: the skeleton hash of the declaration's value, and how many
    distinct nodes that skeleton has. A declaration with no value, or one proved by `rfl`, gets no
    key — `rfl`-proved statements share one skeleton by the thousand and group into noise. -/
private def proofKey (ci : ConstantInfo) : String × Nat :=
  match ci.value? with
  | none => ("", 0)
  | some value =>
    match proofHead value with
    | .const c _ => if c == ``rfl || c == ``Eq.refl then ("", 0) else
        let skel := (skeleton value).run' {}
        (cell skel.hash, skeletonNodes skel)
    | _ =>
      let skel := (skeleton value).run' {}
      (cell skel.hash, skeletonNodes skel)

/-- The `.olean` files of one module under `buildDir`, in the order the module system saves them:
    the main part, then the server and private parts when the module is split. -/
private def oleanParts (buildDir : String) (mod : Name) : Array System.FilePath :=
  let base := System.FilePath.mk (buildDir ++ "/" ++ (toString mod).replace "." "/")
  #[base.addExtension "olean", base.addExtension "olean.server", base.addExtension "olean.private"]

/-- The constants of one module from its parts, one entry per name. The parts overlap: the private
    part holds every constant, the exported and server parts the exported subset, with definitions
    weakened to axioms. The private part comes last, so the last occurrence wins and the weakened
    forms are discarded. Returned as the map, not just its values: an inductive's key needs its
    constructors' types, and they must come from this same merged view or a split module would key
    its inductives off the weakened forms and disagree with an unsplit one. -/
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
      let (proof, nodes) := proofKey ci
      declInfos := declInfos.push (String.intercalate fieldSep
        [name, toString userName, toString mod, kind, cell (declKey consts ci), proof,
         toString nodes, if generatedName userName then "1" else "0"])
      let used := (ci.type.getUsedConstants ++ (ci.value?.map (·.getUsedConstants)).getD #[]).toList.eraseDups
      for dst in used do
        if dst == ci.name then continue
        deps := deps.push s!"{name}{fieldSep}{toString dst}{fieldSep}{toString mod}"
  return { declInfos, deps }

end LeanRefactor.OleanRows
