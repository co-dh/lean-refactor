module

import Lean
import LeanRefactor.Db
-- The public signatures below mention `SyntaxRows.Node` and `FileMap`, which plain imports only
-- bring in privately.
public import LeanRefactor.SyntaxRows
public import Lean.Data.Position

open Lean

namespace LeanRefactor.SyntaxQuery

/-- The `syntax_node` rows `SyntaxRows.ofFile` prints, as structured nodes: the db cell (first) is
    dropped, everything else parses to `SyntaxRows.Node`. -/
public def nodesOfRows (rows : Array String) : Array SyntaxRows.Node :=
  rows.filterMap fun row =>
    match row.splitOn Db.fieldSep with
    | [_module, id, parent, kind, b0, b1, hash, nodes] =>
        match id.toNat?, parent.toInt?, b0.toNat?, b1.toNat?, hash.toNat?, nodes.toNat? with
        | some id, some parent, some b0, some b1, some hash, some nodes =>
            some (SyntaxRows.Node.mk id parent kind b0 b1 hash.toUInt64 nodes)
        | _, _, _, _, _, _ => none
    | _ => none

/-- Every `syntax_node` row of `moduleName` from the index, in id order.  An empty result is a
    module the index has never seen — never built — and the caller decides what that means. -/
public def nodesOfModule (dbPath moduleName : String) : IO (Array SyntaxRows.Node) := do
  let m := Db.escaped moduleName
  let j ← Db.query dbPath
    s!"select n.id as id, n.parent as parent, k.name as kind, n.b0 as b0, n.b1 as b1,
              n.hash as hash, n.nodes as nodes
       from syntax_node n join module m on m.id = n.module join syntax_kind k on k.id = n.kind
       where m.name = '{m}' order by n.id"
  match j with
  | .arr rows =>
      return rows.filterMap fun row => do
        let id ← (row.getObjValAs? Nat "id").toOption
        let parent ← (row.getObjValAs? Int "parent").toOption
        let kind ← (row.getObjValAs? String "kind").toOption
        let b0 ← (row.getObjValAs? Nat "b0").toOption
        let b1 ← (row.getObjValAs? Nat "b1").toOption
        let hash ← (row.getObjValAs? Nat "hash").toOption
        let nodes ← (row.getObjValAs? Nat "nodes").toOption
        pure (SyntaxRows.Node.mk id parent kind b0 b1 hash.toUInt64 nodes)
  | _ => return #[]

/-- The tree of a module the index cannot answer for, by elaborating it in THIS process: the
    elaboration is the expensive part, and the caller has already decided it cannot be skipped. -/
public def nodesOfFile (path moduleName : String) : IO (Array SyntaxRows.Node) := do
  let rows ← SyntaxRows.ofFile path moduleName
  pure (nodesOfRows rows.nodes)

/-- One declaration the source writes, as the tree reads it.  `slot` and `attributes` answer the
    two questions the marking pass asks: where `public ` goes, and whether an existing attribute
    bracket has to be joined rather than preceded. -/
public structure Decl where
  keyword : String     -- as written: `def`, `theorem`, `instance`, `structure`, `class`, `abbrev`,
                       -- `inductive`, `opaque`, `example`
  name : String        -- as written, without the namespace it sits in; "" for anonymous declarations
  namePos : Nat        -- byte of `name`; the keyword byte when anonymous
  kw : Nat             -- byte of the declaration keyword
  slot : Nat           -- byte where `public ` goes: the first modifier after the last attribute
                       -- bracket, or the keyword when none
  visibility : String  -- "public" or "private" when the source fixes it, "" otherwise
  attributes : Option (Nat × Nat)  -- the last `@[ ... ]` bracket: (byte of `@`, byte just past `]`)

/-- The words that introduce a declaration, as the head of every `declaration` root spells one.
    `example` is here so its roots are recognised and then left alone — nothing outside the file
    can name one, and the marking pass never touches them. -/
private def declKeywords : Array String :=
  #["def", "theorem", "abbrev", "instance", "structure", "class", "inductive", "opaque", "axiom",
    "example"]

/-- The first node in `root`'s subtree satisfying `test`, in preorder — which is also the one with
    the smallest `b0`, since ids are assigned in preorder.  Both uses search no deeper than the
    `declId`; the recursion would only go deeper when the search fails. -/
private partial def firstOf (children : Std.HashMap Int (Array SyntaxRows.Node))
    (test : SyntaxRows.Node → Bool) (root : Nat) : Option SyntaxRows.Node := Id.run do
  for k in children.getD root #[] do
    if test k then return some k
  for k in children.getD root #[] do
    if let some hit := firstOf children test k.id then return some hit
  return none

/-- One modifier the source wrote on a declaration: an attribute bracket, a docstring, a
    visibility word, or an `afterVisibility` word like `noncomputable`.  Empty modifier slots are
    filtered out before this is built. -/
private structure Modifier where
  b0 : Nat
  b1 : Nat
  kind : String

/-- The declarations the source writes, in file order, from the flattened tree of its commands.
    Every `declaration` root has exactly two children: the always-present `declModifiers` node,
    whose children are one `null` wrapper per modifier slot — including slots Lean left unwritten,
    whose range is (0, 0) — and the head, whose keyword comes first. -/
public def declarationsOf (nodes : Array SyntaxRows.Node) (source : String) : Array Decl := Id.run do
  -- Keyed by `Int` because a root command's `parent` is -1; the guard keeps roots out of the map,
  -- and every lookup coerces the `Nat` id of a node to `Int` for free.
  let children : Std.HashMap Int (Array SyntaxRows.Node) := Id.run do
    let mut m : Std.HashMap Int (Array SyntaxRows.Node) := {}
    for n in nodes do
      if n.parent >= 0 then
        let siblings := (m.getD n.parent #[]).push n
        m := m.insert n.parent siblings
    m
  let slice (b0 b1 : Nat) : String := String.Pos.Raw.extract source ⟨b0⟩ ⟨b1⟩
  let mut out := #[]
  for root in nodes do
    unless root.kind == "Lean.Parser.Command.declaration" do continue
    let kids := children.getD root.id #[]
    let dm := kids.find? (·.kind == "Lean.Parser.Command.declModifiers")
    let head := kids.find? (·.kind != "Lean.Parser.Command.declModifiers")
    if let some head := head then
      let kwNode := firstOf children
        (fun n => n.b1 > 0 && declKeywords.contains (slice n.b0 n.b1)) head.id
      let kw := kwNode.map (·.b0) |>.getD head.b0
      let keyword := kwNode.map (fun n => slice n.b0 n.b1) |>.getD ""
      let mods : Array Modifier := (match dm with
        | some dm => (children.getD dm.id #[]).filterMap fun w => Id.run do
            -- an unwritten modifier slot is a `null` wrapper with range (0, 0)
            if w.b1 == 0 then none
            else let m := (children.getD w.id #[]).find? (·.b1 > 0) |>.getD w
                 some { b0 := m.b0, b1 := m.b1, kind := m.kind }
        | none => #[])
      let attributes : Option (Nat × Nat) :=
        (mods.filter (·.kind == "Lean.Parser.Term.attributes")).foldl
          (fun (best : Option (Nat × Nat)) (m : Modifier) =>
            if best.all (·.2 < m.b1) then some (m.b0, m.b1) else best) none
      let run := (match attributes with
        | some a => mods.filter (fun m : Modifier => m.b0 ≥ a.2)  -- after the last attribute bracket
        | none => mods).filter (fun m : Modifier => m.kind != "Lean.Parser.Command.docComment")
      let visibility := match run.find? (fun m : Modifier =>
          m.kind == "Lean.Parser.Command.public" || m.kind == "Lean.Parser.Command.private") with
        | some m => slice m.b0 m.b1
        | none => ""
      let slot := match run[0]? with
        | some m => m.b0
        | none => kw
      let ident := (firstOf children (·.kind == "Lean.Parser.Command.declId") head.id).bind
        (fun declId => (children.getD declId.id #[]).find? (·.kind == "ident"))
      let namePos := ident.map (·.b0) |>.getD kw
      let name := ident.map (fun n => slice n.b0 n.b1) |>.getD ""
      out := out.push { keyword, name, namePos, kw, slot, visibility, attributes }
  out

/-- The 0-based lines that start an `instance` command — the seeds the public closure has to be
    run from as well, since nothing in the olean says which definitions are instances.  Seeds, not
    marks: `Freyd.S2_155_BiEntire`'s `instCatB` names `BObj` and `BHom` in its own signature, and
    making the instance public without the closure only moved the error to `a private declaration
    exists but would need to be public to access here`. -/
public def instanceLinesOf (decls : Array Decl) (source : String) : Array Nat := Id.run do
  let fileMap := FileMap.ofString source
  decls.filterMap fun d =>
    if d.keyword == "instance" then some (fileMap.toPosition ⟨d.kw⟩).line.pred else none

/-- The declaration the index's site `declName` at `(line, column)` means.  The name matches the
    source's written name by suffix at a component boundary, longest first — the same rule the
    text-scanning pass used; the site's position is a tiebreak for the file that writes the same
    name twice, and the only handle an anonymous instance has, whose name the source never writes. -/
public def matchDecl (decls : Array Decl) (declName : String) (line column : Nat)
    (fileMap : FileMap) : Option Decl := Id.run do
  let byte := (fileMap.lspPosToUtf8Pos ⟨line, column⟩).byteIdx
  let named := decls.filter (fun d => !d.name.isEmpty &&
    (declName == d.name || declName.endsWith ("." ++ d.name)))
  if let some d := named.find? (fun d => d.namePos == byte) then return some d
  if let some d := decls.find? (fun d => d.kw == byte) then return some d
  named.foldl (fun best d => if best.all (·.name.length < d.name.length) then some d else best) none

/-- The declaration whose name is the parent of `declName`'s last component — the structure,
    inductive, or def a field, constructor, or recursor belongs to, when the index names the member
    instead of the declaration itself.  A public structure publishes its projections, so
    `Freyd.HashMap.AHashMap.buckets` is published by marking `AHashMap` — the field site is not an
    error, it is the parent's mark.  Longest name wins, like `matchDecl`; the dot before `d.name`
    is a component boundary, so a site can never match a similarly-named sibling. -/
public def memberOf (decls : Array Decl) (declName : String) : Option Decl := Id.run do
  let parent := String.intercalate "." ((declName.splitOn ".").dropLast)
  if parent.isEmpty then return none
  decls.foldl (fun (best : Option Decl) (d : Decl) =>
    if (parent == d.name || parent.endsWith ("." ++ d.name))
        && best.all (·.name.length < d.name.length) then some d else best) none

/-- The identifier the tree covers at byte `p` — "" when the position is on whitespace,
    punctuation, or a keyword atom.  The word the old text pass compared against the site name's
    components, kept for the one benign mismatch it could tolerate: a position whose word still
    belongs to a name the file no longer contains as a declaration.  Preorder puts an ancestor
    before its descendants, so the LAST covering `ident` node is the innermost. -/
public def wordAt (nodes : Array SyntaxRows.Node) (source : String) (p : Nat) : String :=
  match nodes.foldl (fun (best : Option SyntaxRows.Node) (n : SyntaxRows.Node) =>
      if n.kind == "ident" && n.b0 <= p && p < n.b1 then some n else best) none with
  | some n => String.Pos.Raw.extract source ⟨n.b0⟩ ⟨n.b1⟩
  | none => ""

end LeanRefactor.SyntaxQuery
