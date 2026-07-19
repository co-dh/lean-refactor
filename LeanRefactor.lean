module

import Lean

/-!
`lean-refactor` performs conservative source edits using two pieces of information produced by Lean:

* `.ilean` reference data identifies uses of a particular global declaration semantically;
* the fully elaborated command syntax tree identifies the enclosing application and its explicit arguments.

The tool previews by default and refuses an edit if a resolved reference is not an ordinary application,
the requested argument is absent, or an original source range is unavailable.  It intentionally does not
fall back to textual matching.
-/

open Lean Lean.Parser Lean.Server

namespace LeanRefactor

structure ReferenceSite where
  range : Lean.Lsp.Range
  parent? : Option String
  deriving Repr

structure Edit where
  start : String.Pos.Raw
  stop : String.Pos.Raw
  line : Nat
  deriving Repr

private def usageSites (ilean : Ilean) (declModule declName : String) : Array ReferenceSite :=
  match ilean.references.get? (.const declModule declName) with
  | none => #[]
  | some info => info.usages.map fun loc =>
      { range := loc.range, parent? := loc.parentDecl? }

private def definitionSite? (ilean : Ilean) (declModule declName : String) : Option ReferenceSite := do
  let info ← ilean.references.get? (.const declModule declName)
  let loc ← info.definition?
  some { range := loc.range, parent? := loc.parentDecl? }

private partial def syntaxAt
    (pos : String.Pos.Raw) (stx : Syntax) (parents : List Syntax := []) : Option (Syntax × List Syntax) :=
  let here := match stx.getPos?, stx.getTailPos? with
    | some start, some stop => start ≤ pos && pos < stop
    | _, _ => false
  if !here then none
  else findChild stx.getArgs 0
where
  findChild (children : Array Syntax) (i : Nat) : Option (Syntax × List Syntax) :=
    match children[i]? with
    | none => some (stx, parents)
    | some child => syntaxAt pos child (stx :: parents) |>.orElse fun _ => findChild children (i + 1)

private def parseName (s : String) : Name :=
  (s.splitOn ".").foldl (fun n part => Name.str n part) Name.anonymous

private def enclosingApp (fileMap : FileMap) (site : ReferenceSite)
    (commands : Array Syntax) : Option Syntax := do
  let pos := fileMap.lspPosToUtf8Pos site.range.start
  let (_, parents) ← commands.findSome? (syntaxAt pos)
  parents.find? (·.isOfKind ``Lean.Parser.Term.app)

private def appArgs (app : Syntax) : Option (Array Syntax) := do
  guard (app.isOfKind ``Lean.Parser.Term.app)
  let argsNode ← app.getArgs[1]?
  some argsNode.getArgs

private partial def binderCandidates (binderName : String) (stx : Syntax)
    (parents : List Syntax := []) : Array Syntax := Id.run do
  let mut found := #[]
  if stx.isIdent && stx.getId.toString == binderName then
    if let some binder := parents.find? (fun p =>
        p.isOfKind ``Lean.Parser.Term.explicitBinder ||
        p.isOfKind ``Lean.Parser.Term.implicitBinder ||
        p.isOfKind ``Lean.Parser.Term.instBinder) then
      found := found.push binder
  for child in stx.getArgs do
    found := found ++ binderCandidates binderName child (stx :: parents)
  found

private def declarationBinderEdit (source : String) (fileMap : FileMap) (site : ReferenceSite)
    (commands : Array Syntax) (binderName : String) : Except String Edit := do
  let pos := fileMap.lspPosToUtf8Pos site.range.start
  let some (_, parents) := commands.findSome? (syntaxAt pos)
    | throw "declaration has no original syntax node"
  let some declaration := parents.find? (fun p => p.isOfKind ``Lean.Parser.Command.declaration)
    | throw "resolved definition is not inside a declaration command"
  let candidates := binderCandidates binderName declaration
  if candidates.size != 1 then
    throw s!"expected exactly one binder named `{binderName}` in the declaration, found {candidates.size}"
  let binder := candidates[0]!
  let identifiers := binder.getArgs.foldl (init := #[]) fun acc child =>
    if child.isIdent then acc.push child else acc
  if identifiers.size > 1 then
    throw s!"refusing grouped binder `{binderName}`; split it into a single-name binder first"
  let some range := binder.getRange?
    | throw s!"binder `{binderName}` has no original source range"
  let start := Id.run do
    let mut p := range.start
    while p.byteIdx > 0 do
      let previous := p.unoffsetBy ⟨1⟩
      let char := String.Pos.Raw.extract source previous p
      if char == " " || char == "\t" then p := previous else break
    return p
  pure { start, stop := range.stop, line := (fileMap.toPosition range.start).line }

private def editForSite (fileMap : FileMap) (site : ReferenceSite)
    (commands : Array Syntax) (argIndex : Nat) : Except String Edit := do
  let some app := enclosingApp fileMap site commands
    | throw s!"line {site.range.start.line + 1}: resolved reference is not inside an application"
  let some args := appArgs app
    | throw s!"line {site.range.start.line + 1}: unsupported application syntax"
  let some target := args[argIndex]?
    | throw s!"line {site.range.start.line + 1}: application has only {args.size} explicit argument(s)"
  let some targetRange := target.getRange?
    | throw s!"line {site.range.start.line + 1}: argument has no original source range"
  let start ← if argIndex > 0 then
      let some previous := args[argIndex - 1]?
        | throw "internal argument-index error"
      let some previousRange := previous.getRange?
        | throw s!"line {site.range.start.line + 1}: preceding argument has no source range"
      pure previousRange.stop
    else if let some next := args[1]? then
      let some _ := next.getRange?
        | throw s!"line {site.range.start.line + 1}: following argument has no source range"
      pure targetRange.start
    else
      throw s!"line {site.range.start.line + 1}: refusing to remove the application's sole argument"
  let stop ← if argIndex == 0 then
      let some next := args[1]? | throw "internal argument-index error"
      let some nextRange := next.getRange? | throw "internal source-range error"
      pure nextRange.start
    else pure targetRange.stop
  pure { start, stop, line := site.range.start.line + 1 }

private def applyEdits (source : String) (edits : Array Edit) : String :=
  let edits := edits.qsort fun a b => b.start.byteIdx < a.start.byteIdx
  edits.foldl (init := source) fun text edit =>
    String.Pos.Raw.extract text 0 edit.start ++ String.Pos.Raw.extract text edit.stop text.rawEndPos

private def showContext (fileMap : FileMap) (site : ReferenceSite)
    (commands : Array Syntax) : IO Unit := do
  let pos := fileMap.lspPosToUtf8Pos site.range.start
  let some (_, parents) := commands.findSome? (syntaxAt pos)
    | IO.println s!"{site.range.start.line + 1}:{site.range.start.character + 1}: no syntax node"
      return
  let kinds := parents.take 8 |>.map (toString ·.getKind)
  IO.println s!"{site.range.start.line + 1}:{site.range.start.character + 1}\t{site.parent?.getD "<command>"}"
  IO.println s!"  {String.intercalate " → " kinds}"

private def usage : String :=
  "usage:\n  lean-refactor inspect <source.lean> <module> <declaration-module> <full-declaration-name>\n  lean-refactor remove-call-arg <source.lean> <module> <declaration-module> <full-declaration-name> <1-based-index> [--apply]\n  lean-refactor remove-parameter <source.lean> <module> <full-declaration-name> <binder-name> <1-based-index> [--apply]"

def main (args : List String) : IO UInt32 := do
  let (mode, sourcePath, moduleName, declModule, declName, binderName?, argIndex?, apply) ← match args with
    | ["inspect", sourcePath, moduleName, declModule, declName] =>
        pure ("inspect", sourcePath, moduleName, declModule, declName, none, none, false)
    | ["remove-call-arg", sourcePath, moduleName, declModule, declName, index] =>
        pure ("remove", sourcePath, moduleName, declModule, declName, none, index.toNat?, false)
    | ["remove-call-arg", sourcePath, moduleName, declModule, declName, index, "--apply"] =>
        pure ("remove", sourcePath, moduleName, declModule, declName, none, index.toNat?, true)
    | ["remove-parameter", sourcePath, moduleName, declName, binderName, index] =>
        pure ("parameter", sourcePath, moduleName, moduleName, declName, some binderName, index.toNat?, false)
    | ["remove-parameter", sourcePath, moduleName, declName, binderName, index, "--apply"] =>
        pure ("parameter", sourcePath, moduleName, moduleName, declName, some binderName, index.toNat?, true)
    | _ => IO.eprintln usage; return 2
  let source ← IO.FS.readFile sourcePath
  let inputCtx := Parser.mkInputContext source sourcePath
  let (header, parserState, headerMessages) ← Parser.parseHeader inputCtx
  unless !headerMessages.hasErrors do
    for msg in headerMessages.toList do IO.eprintln (← msg.toString)
    return 1
  initSearchPath (← findSysroot)
  let (env, headerMessages) ← Elab.processHeader header {} headerMessages inputCtx
    (mainModule := parseName moduleName)
  unless !headerMessages.hasErrors do
    for msg in headerMessages.toList do IO.eprintln (← msg.toString)
    return 1
  let frontend ← Elab.IO.processCommands inputCtx parserState (Elab.Command.mkState env {} {})
  unless !frontend.commandState.messages.hasErrors do
    for msg in frontend.commandState.messages.toList do IO.eprintln (← msg.toString)
    return 1
  let commands := frontend.commands
  let ileanPath := System.FilePath.mk ".lake/build/lib/lean" /
    System.FilePath.mk (moduleName.replace "." "/" ++ ".ilean")
  let ilean ← Ilean.load ileanPath
  let sites := usageSites ilean declModule declName
  IO.println s!"{declName}: {sites.size} resolved use(s) in {moduleName}; parsed {commands.size} command(s)"
  if mode == "inspect" then
    for site in sites do showContext inputCtx.fileMap site commands
  else
    let some oneBased := argIndex? | IO.eprintln "argument index must be a positive integer"; return 2
    if oneBased == 0 then IO.eprintln "argument index is 1-based"; return 2
    let mut edits := #[]
    for site in sites do
      match editForSite inputCtx.fileMap site commands (oneBased - 1) with
      | .error message => IO.eprintln message; return 1
      | .ok edit => edits := edits.push edit
    if mode == "parameter" then
      let some binderName := binderName? | IO.eprintln "missing binder name"; return 2
      let warningNeedle := s!"unused variable `{binderName}`"
      let mut hasUnusedWarning := false
      for msg in frontend.commandState.messages.toList do
        if (toString (← msg.data.format)).contains warningNeedle then hasUnusedWarning := true
      unless hasUnusedWarning do
        IO.eprintln s!"refusing: Lean did not report `{binderName}` as unused"
        return 1
      let some definitionSite := definitionSite? ilean declModule declName
        | IO.eprintln "declaration definition is absent from this module's semantic references"
          return 1
      match declarationBinderEdit source inputCtx.fileMap definitionSite commands binderName with
      | .error message => IO.eprintln message; return 1
      | .ok edit => edits := edits.push edit
    for edit in edits do
      let removed := String.Pos.Raw.extract source edit.start edit.stop
      IO.println s!"line {edit.line}: remove {repr removed}"
    if apply then
      IO.FS.writeFile sourcePath (applyEdits source edits)
      IO.println s!"applied {edits.size} edit(s) to {sourcePath}"
    else
      IO.println "preview only; pass --apply to write"
  return 0

end LeanRefactor

public def main (args : List String) : IO UInt32 := LeanRefactor.main args
