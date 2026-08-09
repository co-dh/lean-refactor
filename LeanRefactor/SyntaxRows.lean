module

import Lean
public import LeanRefactor.Db

open Lean

namespace LeanRefactor.SyntaxRows

/-- Every node of one file's command syntax, flattened: `(id, parent, kind, b0, b1)`.

    The tree is the ONE thing in this index that cannot be read back out of an artefact. `.olean`
    holds elaborated constants and `.ilean` holds positions, but neither remembers what was written —
    which is why the marking pass grew 128 lines of hand-rolled brace matching to answer "where does
    this declaration's attribute bracket end", and why two of that migration's failed attempts were
    bugs in exactly those lines.

    Producing it costs a full elaboration: Lean's parser is environment-dependent (this repository
    defines 42 notations, so `a ⊚ b` cannot be parsed without the module that declares `⊚`), so
    there is no cheap parse-only path and the tree is priced like the semantic rows. That is the
    whole argument for storing it. -/
public structure Rows where
  nodes : Array String

/-- One node of the flattened tree. `id` is the node's index in preorder, `parent` the id of the
    enclosing node (-1 for a root command), so a subtree is a contiguous id range and "the innermost
    node covering byte P" is one indexed query rather than a descent. -/
public structure Node where
  id : Nat
  parent : Int
  kind : String
  b0 : Nat
  b1 : Nat
  /-- Hash of the whole subtree, with every identifier blanked and every other token kept. -/
  hash : UInt64
  /-- Nodes in that subtree, itself included — the threshold the duplicate report cuts on. -/
  nodes : Nat

/-- No `atom` column: a token's text is `source[b0:b1]`, and storing it again would roughly double
    the table for nothing. Readers slice the file they are already holding. -/
private def kindOf (stx : Syntax) : String :=
  match stx with
  | .missing    => "missing"
  | .node _ k _ => toString k
  | .atom _ _   => "atom"
  | .ident ..   => "ident"

/-- What a leaf contributes to its subtree hash.

    An `ident` contributes NOTHING but its being an identifier: a proof written for `≤` and its copy
    written for `≥` differ in the constants they name and in nothing else, and that copy is the
    whole reason to look. Every other token contributes its text, so `3` and `5` are not the same
    literal and `+` is not `*` — those are free, since only `ident` and the literal kinds carry text
    a reader cannot recover from the node kind. -/
private def leafHash (stx : Syntax) : UInt64 :=
  match stx with
  | .ident ..    => hash "ident"
  | .atom _ val  => hash val
  | .missing     => hash "missing"
  | .node _ k _  => hash (toString k)

/-- Preorder walk. `id` is the node's index in that order, so a subtree is a contiguous id range and
    "the innermost node covering byte P" is one indexed query rather than a descent.  Each child's
    `parent` is this node's id — the `next` this invocation was given — and the id counter is
    threaded through the children with a fold, so no mutable state is needed.

    An id is assigned on the way DOWN and the subtree hash finished on the way UP, so the node is
    pushed before its children are walked and patched once they are done.  The hash and count come
    back as results rather than being read out of `acc`: rescanning a node's children in the array
    would make the walk quadratic, and one file here runs to ten thousand nodes. -/
private partial def walk (stx : Syntax) (parent : Int) (next : Nat) (acc : Array Node) :
    Nat × Array Node × UInt64 × Nat :=
  let (b0, b1) := match stx.getRange? with
    | some r => (r.start.byteIdx, r.stop.byteIdx)
    | none   => (0, 0)
  let kind := kindOf stx
  let acc := acc.push { id := next, parent, kind, b0, b1, hash := leafHash stx, nodes := 1 }
  let (after, acc, h, nodes) := stx.getArgs.foldl
    (fun (n, acc, h, nodes) child =>
      let (n, acc, kidHash, kidNodes) := walk child next n acc
      (n, acc, mixHash h kidHash, nodes + kidNodes))
    (next + 1, acc, leafHash stx, 1)
  (after, acc.set! next { id := next, parent, kind, b0, b1, hash := h, nodes }, h, nodes)

/-- Flatten the commands of one elaborated file into the preorder node array. -/
public def nodesOfCommands (commands : Array Syntax) : Array Node := Id.run do
  let (_, nodes) := commands.foldl
    (fun (n, acc) cmd => let (n, acc, _, _) := walk cmd (-1) n acc; (n, acc)) (0, #[])
  nodes

/-- Elaborate `path` against its imports and flatten every command it parsed.

    One file, one process: the caller forks. Elaborating in a loop retains an `Environment` per file
    and reached 18.3 GB on this repository before the OOM killer chose a different victim. -/
public def ofFile (path moduleName : String) : IO Rows := do
  let source ← IO.FS.readFile path
  let inputCtx := Parser.mkInputContext source path
  let (header, parserState, headerMessages) ← Parser.parseHeader inputCtx
  if headerMessages.hasErrors then
    throw <| IO.userError s!"{path}: cannot parse the import header"
  initSearchPath (← findSysroot)
  let (env, headerMessages) ← Elab.processHeader header {} headerMessages inputCtx
    (mainModule := moduleName.toName)
  if headerMessages.hasErrors then
    throw <| IO.userError s!"{path}: cannot import {moduleName}'s dependencies"
  let frontend ← Elab.IO.processCommands inputCtx parserState (Elab.Command.mkState env {} {})
  -- Elaboration errors are NOT fatal here. The tree is what the parser produced, and a file that
  -- fails to elaborate is exactly the file a refactor is about to be pointed at.
  return { nodes := (nodesOfCommands frontend.commands).map (fun n =>
    Db.row #[moduleName, toString n.id, toString n.parent, n.kind, toString n.b0, toString n.b1,
             Db.cell n.hash, toString n.nodes]) }

end LeanRefactor.SyntaxRows
