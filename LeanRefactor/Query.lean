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
  let sql := s!"select m.source as source, u.l1 as l1, u.c1 as c1, u.l2 as l2, u.c2 as c2
from use_site u join module m on m.name = u.use_module
where u.name = '{Db.escaped declName}' and u.is_definition = 0"
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
where name = '{Db.escaped declName}' and is_definition = 0 group by use_module order by use_module"
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

/-- What each declaration whose user-facing name contains `fragment` SAYS: its name, the source path
    and 1-based line of that name, and the signature as the source spells it.

    On `user_name`, not `name`: a fragment cannot match through the `_private.…` mangling.  The
    compiler's own declarations are dropped — an equation lemma repeats its parent's signature. -/
public def declStatements (dbPath fragment : String) :
    IO (Array (String × String × Nat × String)) := do
  let j ← Db.query dbPath s!"select i.user_name as n, m.source as s, r.sl1 + 1 as l, i.stmt as t
from decl_info i
join module m on m.name = i.module
join decl_range r on r.name = i.name and r.module = i.module
where i.user_name like '%{Db.escaped fragment}%' and i.internal = 0 and i.stmt != ''
order by m.source, r.sl1"
  match j with
  | .arr rows =>
      return rows.filterMap fun row => do
        let n ← (row.getObjValAs? String "n").toOption
        let s ← (row.getObjValAs? String "s").toOption
        let l ← (row.getObjValAs? Nat "l").toOption
        let t ← (row.getObjValAs? String "t").toOption
        pure (n, s, l, t)
  | _ => return #[]

/-- The source paths that DECLARE `declName`, and the module names with them.  This is what lets a
    command take a declaration and no file: the index already knows where the binding site is, so
    naming the file at the call site only repeats what it says.  Normally one row; two mean the same
    name is declared in two modules, and the caller has to say which with the file selector. -/
public def declaringModules (dbPath declName : String) : IO (Array (String × String)) := do
  let j ← Db.query dbPath s!"select distinct m.name as n, m.source as s
from decl_info i join module m on m.name = i.module
where i.user_name = '{Db.escaped declName}' or i.name = '{Db.escaped declName}'
order by m.source"
  match j with
  | .arr rows =>
      return rows.filterMap fun row => do
        let n ← (row.getObjValAs? String "n").toOption
        let s ← (row.getObjValAs? String "s").toOption
        pure (n, s)
  | _ => return #[]

/-- Whether the index knows a MODULE by this name — `Freyd.S1_45`, as an import writes it. -/
public def isModule (dbPath name : String) : IO Bool := do
  let j ← Db.query dbPath s!"select name as m from module where name = '{Db.escaped name}'"
  return !(namedModules j).isEmpty

/-- Modules whose declarations mention `declName` in a type or a proof term, name-sorted. -/
public def dependentModules (dbPath declName : String) : IO (Array String) := do
  let j ← Db.query dbPath s!"select distinct module as m from dep where dst = '{Db.escaped declName}' order by module"
  return (namedModules j)

/-- Modules that depend on `declName` without naming it anywhere the info trees recorded: they reach it
    through notation or macro expansion.  No edit is needed there — the notation is declared once — but
    they are exactly the modules a rename can break without touching. -/
public def silentDependents (dbPath declName : String) : IO (Array String) := do
  let j ← Db.query dbPath s!"select distinct module as m from dep where dst = '{Db.escaped declName}'
except select distinct use_module from use_site where name = '{Db.escaped declName}' and is_definition = 0
order by 1"
  return (namedModules j)

/-- One member of a duplicate group: what it is called, where it is, and how big it is. -/
public structure DupMember where
  name : String
  module : String
  source : String
  line : Nat
  size : Nat

/-- Declarations that share a duplicate key, as groups of two or more.

    `column` picks which key: `stmt_key` groups declarations that STATE the same thing however they
    were proved, `skel` groups those whose proof term has the same shape however they are stated.
    Neither is the syntax key `cloneGroups` uses, and none of the three subsumes another.

    `minSize` is a floor on the skeleton's node count, which is 0 for a statement-keyed row and so
    does not filter one.  Compiler-written declarations are dropped: an equation lemma repeats its
    parent's statement, and there are thousands of them. -/
public def dupGroups (dbPath column : String) (minSize : Nat) : IO (Array (Array DupMember)) := do
  let j ← Db.query dbPath s!"select i.{column} as k, i.user_name as n, i.module as md, m.source as s,
       coalesce(r.sl1 + 1, 0) as l, i.skel_size as z
from decl_info i
join module m on m.name = i.module
left join decl_range r on r.name = i.name and r.module = i.module
where i.internal = 0 and i.{column} is not null and i.{column} != 0 and i.skel_size >= {minSize}
  and i.{column} in (
    select {column} from decl_info
     where internal = 0 and {column} is not null and {column} != 0 and skel_size >= {minSize}
     group by {column} having count(distinct user_name) > 1)
order by k, m.source, l"
  let mut byKey : Std.HashMap String (Array DupMember) := {}
  let mut order : Array String := #[]
  match j with
  | .arr rows =>
      for row in rows do
        let get (f : String) := (row.getObjValAs? String f).toOption
        let getN (f : String) := (row.getObjValAs? Nat f).toOption
        -- sqlite3 prints the key as a number; it is only ever a grouping token here.
        let k := (get "k").getD (toString ((getN "k").getD 0))
        match get "n", get "md", get "s", getN "l", getN "z" with
        | some name, some module, some source, some line, some size =>
            unless byKey.contains k do order := order.push k
            byKey := byKey.insert k ((byKey.getD k #[]).push { name, module, source, line, size })
        | _, _, _, _, _ => pure ()
  | _ => pure ()
  -- Biggest first, as `dup` orders its groups: the head of the report is the work.
  let groups := order.filterMap (byKey[·]?) |>.filter (·.size > 1)
  return groups.qsort fun a b =>
    let sz (g : Array DupMember) := g.foldl (fun m d => max m d.size) 0
    sz a > sz b || (sz a == sz b && a.size > b.size)

/-- The direct import edges, as `module → the modules it imports`. -/
public def importEdges (dbPath : String) : IO (Std.HashMap String (Array String)) := do
  let j ← Db.query dbPath "select src as a, dst as b from import_edge"
  let mut direct : Std.HashMap String (Array String) := {}
  match j with
  | .arr rows =>
      for row in rows do
        match (row.getObjValAs? String "a").toOption, (row.getObjValAs? String "b").toOption with
        | some a, some b => direct := direct.insert a ((direct.getD a #[]).push b)
        | _, _ => pure ()
  | _ => pure ()
  return direct

/-- One occurrence of a repeated piece of source: its file and the byte range covering it. -/
public structure CloneSite where
  source : String
  b0 : Nat
  b1 : Nat

/-- One group of occurrences that are the same code, and the size of that code in tree nodes. -/
public structure CloneGroup where
  nodes : Nat
  sites : Array CloneSite

/-- Pieces of source written more than once, biggest first.

    A group is a set of syntax subtrees with one hash — the same code up to the identifiers in it,
    since `SyntaxRows` blanks every `ident` and keeps every other token. `minNodes` is the floor on
    subtree size: below it every file agrees by accident.

    Only MAXIMAL groups are reported. A clone's every subtree is a clone too, so a 200-node
    duplicate would otherwise arrive with two hundred smaller copies of its own report. A group is
    dropped when all of its occurrences sit inside one bigger repeated thing: no occurrence is a
    root command, all their parents hash alike, and that parent hash repeats at least as often —
    then the parent's group says everything this one would. A fragment that ALSO occurs somewhere
    its parent does not repeat keeps its group, which is the case that matters: the shared step
    inside two shared proofs is worth naming once. -/
public def cloneGroups (dbPath : String) (minNodes : Nat) : IO (Array CloneGroup) := do
  let sql := s!"with big as (
  select n.hash as h, n.module as md, n.parent as pa, n.b0 as b0, n.b1 as b1, n.nodes as nodes
  from syntax_node n where n.nodes >= {minNodes}
),
grp as (select h, count(*) as c from big group by h having count(*) > 1),
parented as (
  select b.h as h, p.hash as ph from big b join grp on grp.h = b.h
  left join syntax_node p on p.module = b.md and p.id = b.pa
),
interior as (
  select t.h from (
    select h, count(*) as n, count(distinct ph) as kinds, min(ph) as ph,
           sum(case when ph is null then 1 else 0 end) as roots
    from parented group by h
  ) t join grp g on g.h = t.ph
  where t.roots = 0 and t.kinds = 1 and g.c >= t.n
)
select b.nodes as nodes,
       group_concat(m.source, char(31)) as ss,
       group_concat(b.b0, char(31)) as b0s,
       group_concat(b.b1, char(31)) as b1s
from big b join grp on grp.h = b.h join module m on m.id = b.md
where b.h not in (select h from interior)
group by b.h order by b.nodes desc, count(*) desc"
  let j ← Db.query dbPath sql
  match j with
  | .arr rows =>
      let mut out := #[]
      for row in rows do
        let nodes := (row.getObjValAs? Nat "nodes").toOption.getD 0
        let sources := ((row.getObjValAs? String "ss").toOption.getD "").splitOn "\x1f"
        let b0s := ((row.getObjValAs? String "b0s").toOption.getD "").splitOn "\x1f"
        let b1s := ((row.getObjValAs? String "b1s").toOption.getD "").splitOn "\x1f"
        if sources.length == b0s.length && sources.length == b1s.length then
          let sites := (sources.zip (b0s.zip b1s)).toArray.filterMap fun (s, b0, b1) =>
            match b0.toNat?, b1.toNat? with
            | some b0, some b1 => some { source := s, b0, b1 : CloneSite }
            | _, _ => none
          -- File order, so the occurrences of one clone read as a list a reader can walk down.
          out := out.push { nodes, sites := sites.qsort fun a b =>
            a.source < b.source || (a.source == b.source && a.b0 < b.b0) }
      return out
  | _ => return #[]

/-- The public set of one module, as the three tables both queries below select from: what a public
    body may not name (`tainted`), what is public for a reason of its own (`named`), and what those
    drag in after them (`reachable`).  Shared, because a check that disagreed with the pass it
    guards would be worse than no check at all. -/
private def publicSetCTE (m onInstanceLine : String) : String :=
  s!"with recursive tainted(n) as (
  select d.src from dep d
  where d.module = '{m}' and d.dst like '\\_private%' escape '\\'
  union
  select d.src from dep d join tainted on d.dst = tainted.n
    join decl_info a on a.name = tainted.n and a.module = '{m}' and a.internal = 1
  where d.module = '{m}'
),
named(n) as (
  select i.name from decl_info i
  where i.module = '{m}' and i.name not like '\\_private%' escape '\\'
    and (exists (select 1 from dep d where d.dst = i.name and d.module != '{m}')
         or exists (select 1 from use_site s where s.name = i.name and s.use_module != '{m}'
                    and s.is_definition = 0)
         or exists (select 1 from use_site s join dep p on p.src = s.parent
                    where s.name = i.name and s.use_module = '{m}' and s.is_definition = 0
                      and p.dst in ('Lean.ParserDescr', 'Lean.TrailingParserDescr', 'Lean.Macro',
                                    'Lean.Elab.Tactic.Tactic'))
         -- An instance whose body names a private constant is left where it is: publishing it
         -- would demand the source drop that `private`, and nothing outside has asked for it.
         or (i.name not in (select n from tainted)
             and (exists (select 1 from decl_range r where r.name = i.name and r.module = '{m}'
                          and r.sl1 in ({onInstanceLine}))
                  or exists (select 1 from use_site s where s.name = i.name and s.use_module = '{m}'
                             and s.is_definition = 1 and s.l1 in ({onInstanceLine}))))
         -- A definition of this module names it in its TYPE.  The code generator infers a
         -- compilation type on both sides of the module boundary and demands they agree, so every
         -- definition the type has to reduce through must be exposed — and exposure needs `public`.
         -- `abbrev dNat : RelSet := ⟨Nat⟩` is named by nothing outside its file, so no other clause
         -- reaches it, while `con_exp : (Fobj Unit Bit dNat).carrier → Nat` cannot compile without
         -- it.  `def` on both sides: a theorem's statement is never compiled, and a structure or an
         -- inductive publishes its own reduction.
         or exists (select 1 from dep d join decl_info s on s.name = d.src and s.module = d.module
                    where d.dst = i.name and d.module = '{m}' and d.in_type = 1
                      and s.kind = 'def' and i.kind = 'def'))
),
reachable(n) as (
  select n from named
  union
  select d.dst from dep d join reachable on d.src = reachable.n where d.module = '{m}'
)"

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
  let m := Db.escaped moduleName
  -- `in ()` is not SQL, and no line is negative.
  let onInstanceLine :=
    if instanceLines.isEmpty then "-1"
    else String.intercalate ", " (instanceLines.toList.map toString)
  let j ← Db.query dbPath <| publicSetCTE m onInstanceLine ++ s!"
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

/-- The `private` declarations that stand in the way of putting `moduleName` on the module system,
    as (instance, private constant it names, whether anything outside needs the instance).

    An instance is public whether or not anything outside names it — typeclass resolution consults
    it while elaborating every public signature — and a public instance publishes its BODY, with or
    without `@[expose]`: four lines reproduce it, `public instance : Inhabited Nat := ⟨hidden⟩` over
    a `private def hidden`, and Lean answers `a private declaration hidden exists but would need to
    be public to access here`.  So an instance whose body names a private constant cannot be
    converted while that constant stays private, and no marking this pass could write would help.

    A private constant named in the PROOF of a public theorem is not a blocker and is not reported:
    an unexposed theorem publishes its statement only.  That is the difference between the 417
    private constants this repository names from non-private ones and the handful that actually
    stop a build.

    The taint follows the instance's INTERNAL auxiliaries, which are published as part of it, and
    stops at its public dependencies, which answer for their own bodies. -/
public def privateBlockers (dbPath moduleName : String) (instanceLines : Array Nat) :
    IO (Array (String × String × Bool)) := do
  let m := Db.escaped moduleName
  let onInstanceLine :=
    if instanceLines.isEmpty then "-1"
    else String.intercalate ", " (instanceLines.toList.map toString)
  let j ← Db.query dbPath <| publicSetCTE m onInstanceLine ++ s!",
-- The instances this pass will actually mark. Being on an instance line is not enough and neither
-- is an outside dependency: `Freyd.functorCat_hasPullbacks` has no dependant outside its file and
-- is still marked, because a public body in the file names it and the closure carries it along.
seeded(n) as (
  select i.name from decl_info i
  join reachable on reachable.n = i.name
  left join decl_range r on r.name = i.name and r.module = i.module
  left join use_site u on u.name = i.name and u.use_module = i.module and u.is_definition = 1
  where i.module = '{m}' and i.internal = 0 and i.name not like '\\_private%' escape '\\'
    and (r.sl1 in ({onInstanceLine}) or u.l1 in ({onInstanceLine}))
),
published(root, n) as (
  select n, n from seeded
  union
  select published.root, d.dst from dep d join published on d.src = published.n
    join decl_info a on a.name = d.dst and a.module = '{m}' and a.internal = 1
  where d.module = '{m}'
)
select distinct r.user_name as i, b.user_name as p,
       case when exists (select 1 from dep x where x.dst = published.root and x.module != '{m}')
              or exists (select 1 from use_site s where s.name = published.root
                         and s.use_module != '{m}' and s.is_definition = 0)
            then 1 else 0 end as n
from published
join dep d on d.src = published.n and d.module = '{m}'
join decl_info b on b.name = d.dst and b.module = '{m}'
join decl_info r on r.name = published.root and r.module = '{m}'
where d.dst like '\\_private%' escape '\\'
order by i, p"
  match j with
  | .arr rows =>
      return rows.filterMap fun row => do
        let i ← (row.getObjValAs? String "i").toOption
        let p ← (row.getObjValAs? String "p").toOption
        let n ← (row.getObjValAs? Nat "n").toOption
        pure (i, p, n == 1)
  | _ => return #[]

/-- One node of the dependency graph: what the source calls the declaration, what it is, where it
    is written, and what it says. -/
public structure GraphNode where
  name : String
  kind : String
  source : String
  line : Nat
  stmt : String

/-- Every declaration the source itself wrote, as graph nodes.  `user_name`, because that is the
    name a reader types and the name the edges below are mapped onto; a declaration the compiler
    wrote has no source line to point at.  A declaration the `.ilean` does not place keeps line 0. -/
public def graphNodes (dbPath : String) : IO (Array GraphNode) := do
  let j ← Db.query dbPath "select i.user_name as n, i.kind as k, m.source as s,
       coalesce(r.sl1 + 1, 0) as l, i.stmt as t
from decl_info i
join module m on m.name = i.module
left join decl_range r on r.name = i.name and r.module = i.module
where i.internal = 0
order by m.source, l"
  match j with
  | .arr rows =>
      return rows.filterMap fun row => do
        let name ← (row.getObjValAs? String "n").toOption
        let kind ← (row.getObjValAs? String "k").toOption
        let source ← (row.getObjValAs? String "s").toOption
        let line ← (row.getObjValAs? Nat "l").toOption
        pure { name, kind, source, line, stmt := (row.getObjValAs? String "t").toOption.getD "" }
  | _ => return #[]

/-- The dependency edges under the names `graphNodes` gives its nodes.  `dep` stores the MANGLED
    name, so both ends are joined back through `decl_info`; an end that is a compiler-written
    declaration has no node and the join drops the row.  `src` is joined on its module too, which is
    the module the edge was recorded in, so a name declared twice cannot multiply the row. -/
public def graphEdges (dbPath : String) : IO (Array (String × String)) := do
  let j ← Db.query dbPath "select distinct a.user_name as s, b.user_name as t
from dep d
join decl_info a on a.name = d.src and a.module = d.module and a.internal = 0
join decl_info b on b.name = d.dst and b.internal = 0
where a.user_name != b.user_name"
  match j with
  | .arr rows =>
      return rows.filterMap fun row => do
        let s ← (row.getObjValAs? String "s").toOption
        let t ← (row.getObjValAs? String "t").toOption
        pure (s, t)
  | _ => return #[]

end LeanRefactor.Query
