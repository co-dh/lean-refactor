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

/-- One group of declarations that share a key: what they have in common, and each member as
    `user-name`, source path and module. -/
public structure DupGroup where
  members : Array (String × String × String)

/-- `select` over `decl_info` joined to its source path, collected into groups of two or more.
    `keyColumn` is the column the group is formed on; `extra` narrows the rows first. -/
private def groupsOn (dbPath keyColumn extra : String) : IO (Array DupGroup) := do
  -- Notation and parser declarations (`«term_∩_»` and friends) share one elaborator skeleton by the
  -- dozen and say nothing about duplication, so they never enter a group.
  let sql := s!"with d as (
  select i.user_name as u, m.source as s, i.module as md, i.{keyColumn} as k
  from decl_info i join module m on m.name = i.module
  where i.internal = 0 and i.{keyColumn} != '' and i.user_name not like '%.«term%'
    and i.user_name not like '%.term\\_%' escape '\\' {extra}
)
select k, group_concat(u, char(31)) as us, group_concat(s, char(31)) as ss,
       group_concat(md, char(31)) as ms
from d group by k having count(*) > 1 order by count(*) desc, k"
  let j ← Db.query dbPath sql
  match j with
  | .arr rows =>
      let mut out := #[]
      for row in rows do
        let us := (row.getObjValAs? String "us").toOption.getD ""
        let ss := (row.getObjValAs? String "ss").toOption.getD ""
        let ms := (row.getObjValAs? String "ms").toOption.getD ""
        let names := us.splitOn "\x1f"
        let sources := ss.splitOn "\x1f"
        let modules := ms.splitOn "\x1f"
        if names.length == sources.length && names.length == modules.length then
          -- Module order, so "one canonical plus its stragglers" reads apart from "N independent leaves".
          let members := (names.zip (sources.zip modules)).toArray
          out := out.push { members := members.qsort fun a b => a.2.2 < b.2.2 }
      return out
  | _ => return #[]

/-- Declarations stating the same thing: equal `stmt_key` is the elaborated statement up to binder
    and universe renaming, so for a theorem it is the same fact however it was proved, and for a
    definition it is type AND body, i.e. a copy-paste. -/
public def statementGroups (dbPath : String) : IO (Array DupGroup) :=
  groupsOn dbPath "stmt_key" ""

/-- Declarations with the same proof, whatever their statements say. Proofs below `minNodes` distinct
    skeleton nodes are dropped: short ones collide en masse and carry no signal. -/
public def proofGroups (dbPath : String) (minNodes : Nat) : IO (Array DupGroup) :=
  groupsOn dbPath "proof_key" s!"and i.proof_nodes >= {minNodes}"

/-- Where in the source each declaration of `module` sits that the module system would have to mark
    `public`.  The position is the 0-based LSP start of the declaration's NAME, so marking a file
    needs no parse.

    Three things make a declaration public, and the first alone is not enough — each of the other
    two was a failed whole-repository build.

    1. Something outside DEPENDS on it: a `dep` edge from another module.

    2. Something outside NAMES it without depending on it.  `simp only [compFunctor_obj]` writes the
       name in tactic syntax and the finished proof term does not mention it, so there is no edge —
       and `Freyd.S1_14` and `Freyd.S1_74` stopped compiling for exactly that lemma.  The `.ilean`
       reference half records the occurrence, so `use_site` sees what `dep` cannot.

    3. A public declaration's BODY mentions it, transitively, inside this module.  Marking the file
       `@[expose]` publishes the bodies, so everything a body names has to be reachable too.
       `Freyd.Colim.setoid` is public; its `setoid._proof_1` names `rel_symm` and `rel_trans`, which
       nothing outside depends on and which were therefore left private.  The closure follows the
       compiler's own auxiliaries, which is how it gets from `setoid` to `rel_symm` at all.

    `decl_range` answers first, and the BINDING SITE in `use_site` fills its gaps, because the
    `.ilean`'s two halves disagree: its `decls` section drops declarations its `references` section
    still records the definition of — `Freyd.Monic`, named by 101 other modules, is absent from
    `decl_range` and present as a binding site.  Measured on `Freyd.S1_41`: 14 binding sites against
    10 ranges, and the difference was exactly the declarations whose missing `public` failed the
    build.  The order matters the other way too: for a structure the binding site can land on a
    field's binder rather than on the type's own name, so it is the fallback and not the answer.
    No declaration in this repository has two binding sites, so the join cannot duplicate a row.

    4. A notation NAMES it.  A `notation` command needs no marking of its own — it is exported
       across a module boundary as it stands, and `public` is not even accepted before it — but that
       is exactly why what it expands to has to be public: `infixr " ⊛ " => UnderHom.comp` in
       `Freyd.S1_26` and `notation S " ∈ᶠ " F => Filter.Mem S F` in `Freyd.S1_646_Ultrafilter` both
       failed on `Unknown constant _private.…`.  Only `use_site` knows the link — the expansion is
       syntax, so the parser constant has no edge to the function, and the elaborated terms
       downstream name the function and never the parser constant.  The declarations that carry
       exported syntax are recognised by what they are built from: a `ParserDescr` (the notation
       itself), a `Macro` (the rule that expands it) or a tactic elaborator.

    5. It is an INSTANCE, or a public one's signature names it.  Typeclass resolution consults every
       instance while elaborating a public signature and leaves no trace of what it found — the
       coercion or the class field is unfolded into the term — so `Freyd.S2_20`'s `CoeFun` instance
       has neither an edge nor a reference anywhere here, and the theorem whose statement applies
       `D` to an argument failed with `Function expected`.  The caller reads the instance lines off
       the source, which is the only place that says which definitions are instances; they enter as
       SEEDS, so the closure below carries `Freyd.S2_155_BiEntire`'s `instCatB` on to the `BObj` and
       `BHom` its own signature names.

    Declarations the source already marks `private` are excluded: they are mangled to `_private.…`
    and stay module-local either way.  So are the ones neither half places — a structure field or a
    derived instance, which the source never writes and which inherits its parent's visibility.

    The last field says whether the body may be EXPOSED, which a `private` dependency forbids:
    publishing a body that names a constant no one downstream can name is not possible, and
    `Freyd.S2_165_Spl`'s instance failed on exactly that, one step removed — its own `_proof_1`
    names the `private theorem splObj_semiSimple_of_ssd`.  So the taint follows a declaration's
    INTERNAL auxiliaries, which are published with it, and stops at its public dependencies, which
    are published on their own terms. -/
public def publicDeclSites (dbPath moduleName : String) (instanceLines : Array Nat) :
    IO (Array (String × Nat × Nat × Bool)) := do
  let m := escaped moduleName
  -- `in ()` is not SQL, and no line is negative.
  let onInstanceLine :=
    if instanceLines.isEmpty then "-1"
    else String.intercalate ", " (instanceLines.toList.map toString)
  let j ← Db.query dbPath s!"with recursive named(n) as (
  select i.name from decl_info i
  where i.module = '{m}' and i.name not like '\\_private%' escape '\\'
    and (exists (select 1 from dep d where d.dst = i.name and d.module != '{m}')
         or exists (select 1 from use_site s where s.name = i.name and s.use_module != '{m}'
                    and s.is_definition = 0)
         or exists (select 1 from use_site s join dep p on p.src = s.parent
                    where s.name = i.name and s.use_module = '{m}' and s.is_definition = 0
                      and p.dst in ('Lean.ParserDescr', 'Lean.TrailingParserDescr', 'Lean.Macro',
                                    'Lean.Elab.Tactic.Tactic'))
         or exists (select 1 from decl_range r where r.name = i.name and r.module = '{m}'
                    and r.sl1 in ({onInstanceLine}))
         or exists (select 1 from use_site s where s.name = i.name and s.use_module = '{m}'
                    and s.is_definition = 1 and s.l1 in ({onInstanceLine})))
),
reachable(n) as (
  select n from named
  union
  select d.dst from dep d join reachable on d.src = reachable.n where d.module = '{m}'
),
tainted(n) as (
  select d.src from dep d
  where d.module = '{m}' and d.dst like '\\_private%' escape '\\'
  union
  select d.src from dep d join tainted on d.dst = tainted.n
    join decl_info a on a.name = tainted.n and a.module = '{m}' and a.internal = 1
  where d.module = '{m}'
)
select i.user_name as n, coalesce(r.sl1, u.l1) as l, coalesce(r.sc1, u.c1) as c,
       case when t.n is null then 1 else 0 end as e
from decl_info i
join reachable on reachable.n = i.name
left join decl_range r on r.name = i.name and r.module = i.module
left join use_site u on u.name = i.name and u.use_module = i.module and u.is_definition = 1
left join tainted t on t.n = i.name
where i.module = '{m}' and i.internal = 0 and i.name not like '\\_private%' escape '\\'
  and (r.name is not null or u.name is not null)
order by l, c"
  match j with
  | .arr rows =>
      -- sqlite3 prints integer columns as JSON numbers; a row whose fields do not parse is skipped.
      return rows.filterMap fun row => do
        let n ← (row.getObjValAs? String "n").toOption
        let l ← (row.getObjValAs? Nat "l").toOption
        let c ← (row.getObjValAs? Nat "c").toOption
        let e ← (row.getObjValAs? Nat "e").toOption
        pure (n, l, c, e == 1)
  | _ => return #[]

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
