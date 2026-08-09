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

/-- No `atom` column: a token's text is `source[b0:b1]`, and storing it again would roughly double
    the table for nothing. Readers slice the file they are already holding. -/
private def kindOf (stx : Syntax) : String :=
  match stx with
  | .missing    => "missing"
  | .node _ k _ => toString k
  | .atom _ _   => "atom"
  | .ident ..   => "ident"

/-- Preorder walk. `id` is the node's index in that order, so a subtree is a contiguous id range and
    "the innermost node covering byte P" is one indexed query rather than a descent.  Each child's
    `parent` is this node's id — the `next` this invocation was given — and the id counter is
    threaded through the children with a fold, so no mutable state is needed. -/
private partial def walk (module : String) (stx : Syntax) (parent : Int) (next : Nat)
    (acc : Array String) : Nat × Array String :=
  let (b0, b1) := match stx.getRange? with
    | some r => (r.start.byteIdx, r.stop.byteIdx)
    | none   => (0, 0)
  let acc := acc.push (Db.row
    #[module, toString next, toString parent, kindOf stx, toString b0, toString b1])
  stx.getArgs.foldl (fun (n, acc) child => walk module child next n acc) (next + 1, acc)

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
  let mut nodes := #[]
  let mut next := 0
  for command in frontend.commands do
    let (next', nodes') := walk moduleName command (-1) next nodes
    next := next'; nodes := nodes'
  return { nodes }

end LeanRefactor.SyntaxRows
