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
  replacement : String := ""
  deriving Repr

structure WarningSelector where
  path : String
  line? : Option Nat := none
  column? : Option Nat := none

structure HintWidgetProps where
  range : Lsp.Range
  suggestion : String
  deriving FromJson

private def usageSitesIn (references : Lsp.ModuleRefs) (declModule declName : String) : Array ReferenceSite :=
  match references.get? (.const declModule declName) with
  | none => #[]
  | some info => info.usages.map fun loc =>
      { range := loc.range, parent? := loc.parentDecl? }

private def usageSitesNamed (references : Lsp.ModuleRefs) (declName : String) : Array ReferenceSite := Id.run do
  let mut sites := #[]
  for (ident, info) in references do
    if let .const _ name := ident then
      if name == declName then
        sites := sites ++ info.usages.map fun loc =>
          { range := loc.range, parent? := loc.parentDecl? }
  return sites

private partial def syntaxSitesNamed (fileMap : FileMap) (declName : String) (stx : Syntax) : Array ReferenceSite := Id.run do
  let mut sites := #[]
  let shortName := (declName.splitOn ".").getLastD declName
  if stx.isIdent && (stx.getId.toString == declName || stx.getId.toString == shortName) then
    if let some range := stx.getRange? then
      sites := sites.push {
        range := ⟨fileMap.utf8PosToLspPos range.start, fileMap.utf8PosToLspPos range.stop⟩
        parent? := none
      }
  for child in stx.getArgs do sites := sites ++ syntaxSitesNamed fileMap declName child
  return sites

private def usageSites (ilean : Ilean) (declModule declName : String) : Array ReferenceSite :=
  usageSitesIn ilean.references declModule declName

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
  some <| argsNode.getArgs.filter fun arg => !arg.isOfKind ``Lean.Parser.Term.namedArgument

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

private def binderIdentifiers (binder : Syntax) : Array Syntax :=
  binder.getArgs[1]?.map (·.getArgs.filter (·.isIdent)) |>.getD #[]

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
  let identifiers := binderIdentifiers binder
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

private def binderEditAt (source : String) (fileMap : FileMap) (binder ident : Syntax) : Except String Edit := do
  let some identRange := ident.getRange? | throw "warned binder identifier has no source range"
  let identifiers := binderIdentifiers binder
  if identifiers.size <= 1 then
    let some binderRange := binder.getRange? | throw "warned binder has no source range"
    let start := Id.run do
      let mut p := binderRange.start
      while p.byteIdx > 0 do
        let previous := p.unoffsetBy ⟨1⟩
        let char := String.Pos.Raw.extract source previous p
        if char == " " || char == "\t" then p := previous else break
      return p
    pure { start, stop := binderRange.stop, line := (fileMap.toPosition identRange.start).line }
  else
    let some index := identifiers.findIdx? fun candidate => candidate.getRange? == some identRange
      | throw "warned identifier is absent from its binder"
    let (start, stop) ← if let some next := identifiers[index + 1]? then
      let some nextRange := next.getRange? | throw "next binder identifier has no source range"
      pure (identRange.start, nextRange.start)
    else
      let some previous := identifiers[index - 1]? | throw "internal grouped-binder error"
      let some previousRange := previous.getRange? | throw "previous binder identifier has no source range"
      pure (previousRange.stop, identRange.stop)
    pure { start, stop, line := (fileMap.toPosition identRange.start).line }

private def positionalBinderRemovalEdit (source : String) (fileMap : FileMap)
    (ident : Syntax) : Except String Edit := do
  let some range := ident.getRange? | throw "positional binder has no source range"
  let stop := Id.run do
    let mut p := range.stop
    while !p.atEnd source do
      let next := p.next source
      let char := String.Pos.Raw.extract source p next
      if char == " " || char == "\t" then p := next else break
    return p
  pure { start := range.start, stop, line := (fileMap.toPosition range.start).line }

private partial def explicitBinderIndexAt (pos : String.Pos.Raw) (stx : Syntax)
    (count : Nat := 0) : Option Nat × Nat := Id.run do
  let mut count := count
  if stx.isOfKind ``Lean.Parser.Term.explicitBinder then
    for child in binderIdentifiers stx do
      if child.isIdent then
        if let some range := child.getRange? then
          if range.start <= pos && pos < range.stop then return (some count, count)
        count := count + 1
    return (none, count)
  for child in stx.getArgs do
    let (found?, nextCount) := explicitBinderIndexAt pos child count
    if found?.isSome then return (found?, nextCount)
    count := nextCount
  return (none, count)

private def declarationAtPosition? (ilean : Ilean) (pos : Lsp.Position) : Option String := Id.run do
  let mut best : Option (String × Nat) := none
  for (name, info) in ilean.decls do
    let range := info.range
    if range.start <= pos && pos <= range.end then
      let span := range.end.line - range.start.line
      if best.all fun previous => span <= previous.2 then best := some (name, span)
  return best.map (·.1)

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

private def insertionForSite (fileMap : FileMap) (site : ReferenceSite)
    (commands : Array Syntax) (beforeIndex : Nat) (term : String) : Except String Edit := do
  let some app := enclosingApp fileMap site commands
    | throw s!"line {site.range.start.line + 1}: resolved reference is not inside an application"
  let some args := appArgs app | throw "unsupported application syntax"
  let some target := args[beforeIndex]?
    | throw s!"line {site.range.start.line + 1}: application has only {args.size} positional argument(s)"
  let some range := target.getRange? | throw "target argument has no source range"
  pure { start := range.start, stop := range.start, line := site.range.start.line + 1, replacement := term ++ " " }

private def unusedVariableEdits (source : String) (fileMap : FileMap) (commands : Array Syntax)
    (ilean? : Option Ilean) (moduleName binderName : String) (warningPos : Position)
    (tryRemoval := false) : Except String (Array Edit) := do
  let pos := fileMap.ofPosition warningPos
  let some (ident, parents) := commands.findSome? (syntaxAt pos)
    | throw "unused warning has no original syntax node"
  unless ident.isIdent && ident.getId.toString == binderName do
    throw s!"unused warning does not point at binder `{binderName}`"
  -- Safe default: prefix the flagged identifier with `_`.  A name beginning with `_` is exempt from
  -- the unused-variable linter, so this one edit silences the warning for every binder kind — a
  -- top-level parameter, a nested `fun`/`let` binder, or a tactic/pattern binder — while keeping the
  -- original name for documentation.  The linter fires only when the binder has zero references, so
  -- renaming it is always type-correct, and it rewrites no call site, so no `.ilean` data is needed.
  if !tryRemoval then
    let some range := ident.getRange? | throw "unused binder identifier has no source range"
    return #[{ start := range.start, stop := range.start, line := warningPos.line, replacement := "_" }]
  let binder? := parents.find? fun parent =>
    parent.isOfKind ``Lean.Parser.Term.explicitBinder ||
    parent.isOfKind ``Lean.Parser.Term.implicitBinder ||
    parent.isOfKind ``Lean.Parser.Term.instBinder
  let some binder := binder? | do
    let some range := ident.getRange? | throw "unused positional binder has no source range"
    if tryRemoval then return #[← positionalBinderRemovalEdit source fileMap ident]
    return #[{ start := range.start, stop := range.stop, line := warningPos.line, replacement := "_" }]
  let isTopLevelParameter :=
    parents.any (·.isOfKind ``Lean.Parser.Command.declSig) &&
      !parents.any (·.isOfKind ``Lean.Parser.Term.forall)
  unless isTopLevelParameter do
    let some range := ident.getRange? | throw "nested binder identifier has no source range"
    if tryRemoval then return #[← binderEditAt source fileMap binder ident]
    return #[{ start := range.start, stop := range.stop, line := warningPos.line, replacement := "_" }]
  let binderRemoval ← binderEditAt source fileMap binder ident
  unless binder.isOfKind ``Lean.Parser.Term.explicitBinder do return #[binderRemoval]
  let some declaration := parents.find? (·.isOfKind ``Lean.Parser.Command.declaration)
    | throw "explicit unused binder is not inside a declaration"
  let (some argumentIndex, _) := explicitBinderIndexAt pos declaration
    | do
      let some range := ident.getRange? | throw "nested binder identifier has no source range"
      return #[{ start := range.start, stop := range.stop, line := warningPos.line, replacement := "_" }]
  let some ilean := ilean?
    | throw "binder removal needs semantic reference data (.ilean); rebuild the module first"
  let some declName := declarationAtPosition? ilean (fileMap.leanPosToLspPos warningPos)
    | throw "cannot resolve the enclosing declaration name"
  let mut edits := #[binderRemoval]
  for site in usageSites ilean moduleName declName do
    edits := edits.push (← editForSite fileMap site commands argumentIndex)
  pure edits

private def unusedBinderName? (message : String) : Option String := do
  guard (message.contains "unused variable `")
  (message.splitOn "`")[1]?

private def applyEdits (source : String) (edits : Array Edit) : String :=
  let edits := edits.qsort fun a b => b.start.byteIdx < a.start.byteIdx
  edits.foldl (init := source) fun text edit =>
    String.Pos.Raw.extract text 0 edit.start ++ edit.replacement ++
      String.Pos.Raw.extract text edit.stop text.rawEndPos

private def independentEdits (edits : Array Edit) : Array Edit × Nat := Id.run do
  let ordered := edits.qsort fun a b =>
    a.start.byteIdx < b.start.byteIdx ||
      (a.start.byteIdx == b.start.byteIdx && a.stop.byteIdx < b.stop.byteIdx)
  let mut accepted := #[]
  let mut deferred := 0
  for edit in ordered do
    if accepted.any fun prior => edit.start < prior.stop && prior.start < edit.stop then
      deferred := deferred + 1
    else
      accepted := accepted.push edit
  return (accepted, deferred)

private def globMatches (pattern value : String) : Bool :=
  go pattern.toList value.toList
where
  go : List Char → List Char → Bool
    | [], [] => true
    | [], _ => false
    | '*' :: ps, cs => go ps cs || match cs with | [] => false | _ :: cs => go ('*' :: ps) cs
    | '?' :: ps, _ :: cs => go ps cs
    | '?' :: _, [] => false
    | p :: ps, c :: cs => p == c && go ps cs
    | _ :: _, [] => false

private partial def leanFilesUnder (dir : System.FilePath) : IO (Array String) := do
  let mut files := #[]
  for entry in ← dir.readDir do
    if entry.fileName.startsWith "." then
      continue  -- skip .lake, .git, .claude, … : build artefacts and VCS never hold source we edit
    if ← entry.path.isDir then
      files := files ++ (← leanFilesUnder entry.path)
    else if entry.path.extension == some "lean" then
      files := files.push entry.path.toString
  pure files

/-- Repository-relative `.lean` paths matching `pattern`.  Reports and returns empty if none match,
    so every `--glob` subcommand shares one selection rule and one message. -/
private def globSelectedFiles (pattern : String) : IO (Array String) := do
  let files ← leanFilesUnder "."
  let selected := files.map (fun path => if path.startsWith "./" then (path.drop 2).toString else path)
    |>.filter (globMatches pattern)
  if selected.isEmpty then IO.eprintln s!"glob matched no Lean files: {pattern}"
  return selected

private def moduleNameOfPath (path : String) : Except String String := do
  unless path.endsWith ".lean" do throw s!"not a Lean source file: {path}"
  let relative := if path.startsWith "./" then path.drop 2 else path
  if relative.startsWith "/" then throw "source selector must be relative to the repository root"
  pure <| (relative.dropEnd 5).replace "/" "."

private def parseWarningSelector (selector : String) : Except String WarningSelector := do
  let parts := selector.splitOn ":"
  match parts.reverse with
  | column :: line :: restRev =>
      if let some lineNum := line.toNat? then
        let some columnNum := column.toNat?
          | throw s!"invalid warning column in selector: {selector}"
        if lineNum == 0 || columnNum == 0 then throw "warning positions are 1-based"
        pure { path := (String.intercalate ":" restRev.reverse), line? := some lineNum, column? := some columnNum }
      else pure { path := selector }
  | _ => pure { path := selector }

private def tryThisEdits (frontend : Elab.Frontend.State) (fileMap : FileMap) : Array Edit :=
  frontend.commandState.infoState.trees.toArray.foldl (init := #[]) fun edits tree =>
    tree.foldInfo (init := edits) fun _ info edits => Id.run do
      let .ofCustomInfo { value, .. } := info | return edits
      let some hint := value.get? Meta.Tactic.TryThis.TryThisInfo | return edits
      let start := fileMap.lspPosToUtf8Pos hint.edit.range.start
      let stop := fileMap.lspPosToUtf8Pos hint.edit.range.end
      return edits.push { start := start, stop := stop, line := hint.edit.range.start.line + 1, replacement := hint.edit.newText }

private partial def messageHintEdits (data : MessageData) (fileMap : FileMap) : IO (Array Edit) := do
  match data with
  | .ofWidget widget fallback =>
      let (props, _) := widget.props {}
      let fromWidget := match fromJson? props with
        | .ok (hint : HintWidgetProps) =>
            let start := fileMap.lspPosToUtf8Pos hint.range.start
            let stop := fileMap.lspPosToUtf8Pos hint.range.end
            #[{ start := start, stop := stop, line := hint.range.start.line + 1, replacement := hint.suggestion }]
        | .error _ => #[]
      pure (fromWidget ++ (← messageHintEdits fallback fileMap))
  | .withContext _ data | .withNamingContext _ data | .nest _ data | .group data |
      .tagged _ data => messageHintEdits data fileMap
  | .compose left right =>
      pure ((← messageHintEdits left fileMap) ++ (← messageHintEdits right fileMap))
  | .trace _ data children =>
      let mut edits ← messageHintEdits data fileMap
      for child in children do edits := edits ++ (← messageHintEdits child fileMap)
      pure edits
  | _ => pure #[]

/-- Re-elaborate `source` (against the already-imported `env`) and report whether it is error-free.
    Used to reject an edit that would break the build — chiefly an unused-variable *false positive*
    (a binder the linter flags yet a `letI`/`haveI` body actually uses) or a parameter referenced by
    name at a call site.  This is a single in-process elaboration, far cheaper than a `lake build`. -/
private def elaboratesCleanly (env : Environment) (path source : String) : IO Bool := do
  let ctx := Parser.mkInputContext source path
  let (_, parserState, headerMessages) ← Parser.parseHeader ctx
  if headerMessages.hasErrors then return false
  let frontend ← Elab.IO.processCommands ctx parserState (Elab.Command.mkState env {} {})
  pure !frontend.commandState.messages.hasErrors

/-- Keep the largest prefix-safe subset of `edits` whose combined application still elaborates.
    Fast path: if applying them all elaborates cleanly, keep them all (one extra elaboration).  Only
    when that fails do we add edits one at a time, re-checking, so a single breaking edit (a linter
    false positive, a name-referenced parameter) is dropped without discarding the file's safe fixes. -/
private def verifiedEdits (env : Environment) (path source : String) (edits : Array Edit) :
    IO (Array Edit) := do
  if edits.isEmpty then return edits
  if ← elaboratesCleanly env path (applyEdits source edits) then return edits
  let mut kept := #[]
  for edit in edits do
    let candidate := kept.push edit
    if ← elaboratesCleanly env path (applyEdits source candidate) then kept := candidate
  pure kept

private def repositoryBuild : IO IO.Process.Output :=
  IO.Process.output { cmd := "./scripts/cap", args := #["lake", "build", "Freyd"] }

/-! ## Moving a declaration between files

The dedup report (`scripts/dep_dup.py`) flags duplicate groups where no member is importable from all
the others: collapsing those needs the survivor RELOCATED to a module every caller already imports.
That is the one edit the subcommands above cannot express, and the one the skill calls the riskiest
to do by hand, so it is mechanised here: cut the declaration with its docstring, splice it into the
target inside the same namespace, and refuse the edit unless BOTH files still elaborate. -/

/-- Distinct files whose `Environment` this process has built.  Re-elaborating the SAME file is
    routine — `verifiedEdits` does it once per candidate edit — so only distinct paths are counted. -/
initialize elaboratedFiles : IO.Ref (Array String) ← IO.mkRef #[]

/-- `move` legitimately elaborates two files (the source and the target).  Nothing legitimately
    elaborates more, so this cap bounds a process to a constant number of environments. -/
private def maxElaboratedFiles : Nat := 2

/-- Record that `path`'s environment is about to be built; refuse once the cap is reached.

    An `Environment` is retained for as long as anything derived from it lives, so a loop that
    elaborates file after file IN-PROCESS accumulates one per file: `rename --glob 'Freyd/*.lean'`
    reached 18.3 GB resident of 30 GB and was OOM-killed by the kernel twenty minutes in, taking a
    running agent down with it.  `forkPerFile` is the cure, but a convention cannot enforce itself —
    the next in-process loop would reintroduce the leak silently and fail the same slow way.  So the
    bound is CHECKED, here, at the one operation that costs the memory, and a violation fails on the
    third file with the fix named in the message. -/
private def claimElaboration (path : String) : IO Unit := do
  let claimed ← elaboratedFiles.get
  if claimed.contains path then return
  if claimed.size ≥ maxElaboratedFiles then
    throw <| IO.userError <|
      s!"lean-refactor: refusing to build a {claimed.size + 1}th file environment in one process " ++
      s!"({path}; already elaborated {claimed}).  Each one is retained, so looping over files " ++
      "in-process accumulates them and runs the machine out of memory.  Drive the loop with " ++
      "`forkPerFile` instead — one child process per file."
  elaboratedFiles.set (claimed.push path)

/-- Source text, file map and command syntax of `path`.  Lean's parser is extensible, so a file
    using custom notation cannot be parsed without the environment its imports build — hence a full
    elaboration rather than a bare parse. -/
private def elaborateFile (path : String) : IO (String × FileMap × Array Syntax × Environment) := do
  claimElaboration path
  let moduleName ← IO.ofExcept (moduleNameOfPath path)
  let source ← IO.FS.readFile path
  let ctx := Parser.mkInputContext source path
  let (header, parserState, messages) ← Parser.parseHeader ctx
  let (env, messages) ← Elab.processHeader header {} messages ctx (mainModule := parseName moduleName)
  if messages.hasErrors then
    for msg in messages.toList do IO.eprintln (← msg.toString)
    throw <| IO.userError s!"{path}: imports failed to elaborate"
  let frontend ← Elab.IO.processCommands ctx parserState (Elab.Command.mkState env {} {})
  pure (source, ctx.fileMap, frontend.commands, env)

/-- Re-elaborate a whole file (imports included) from candidate `source` text. -/
private def fileElaboratesCleanly (path source : String) : IO Bool := do
  claimElaboration path
  let ctx := Parser.mkInputContext source path
  let (header, parserState, messages) ← Parser.parseHeader ctx
  if messages.hasErrors then return false
  let moduleName := match moduleNameOfPath path with | .ok n => n | .error _ => path
  let (env, messages) ← Elab.processHeader header {} messages ctx (mainModule := parseName moduleName)
  if messages.hasErrors then return false
  elaboratesCleanly env path source

/-- Namespace in force after `cmd`, given the namespace before it and the stack of enclosing scopes.
    `section` is tracked too: it consumes an `end`, so ignoring it would pop the wrong scope. -/
private def scopeStep (state : Name × List Name) (cmd : Syntax) : Name × List Name :=
  let (ns, saved) := state
  if cmd.isOfKind ``Lean.Parser.Command.namespace then
    match cmd.getArgs[1]? with
    | some ident => (ns ++ ident.getId, ns :: saved)
    | none => state
  else if cmd.isOfKind ``Lean.Parser.Command.section then (ns, ns :: saved)
  else if cmd.isOfKind ``Lean.Parser.Command.end then
    match saved with
    | previous :: rest => (previous, rest)
    | [] => state
  else state

/-- The name a `declaration` command introduces, relative to its enclosing namespace. -/
private partial def declIdName? (stx : Syntax) : Option Name :=
  if stx.isOfKind ``Lean.Parser.Command.declId then stx.getArgs[0]?.map (·.getId)
  else stx.getArgs.findSome? declIdName?

/-- Extend a declaration's range to whole lines, absorbing the blank line that follows it, so a cut
    leaves neither a half-line nor a widening run of blanks. -/
private def wholeLines (source : String) (range : Lean.Syntax.Range) : String.Pos.Raw × String.Pos.Raw :=
  let start := Id.run do
    let mut p := range.start
    while p.byteIdx > 0 do
      let previous := p.unoffsetBy ⟨1⟩
      if String.Pos.Raw.extract source previous p == "\n" then break else p := previous
    return p
  let stop := Id.run do
    let mut p := range.stop
    let mut newlines := 0
    while !p.atEnd source && newlines < 2 do
      let next := p.next source
      let char := String.Pos.Raw.extract source p next
      if char == "\n" then newlines := newlines + 1
      else if char != " " && char != "\t" then break
      p := next
    return p
  (start, stop)

/-- Locate `declName` in `commands`: its cut range and the namespace open around it. -/
private def declarationSite (source : String) (commands : Array Syntax) (declName : String) :
    Except String ((String.Pos.Raw × String.Pos.Raw) × Name) := Id.run do
  let wanted := parseName declName
  let mut state := (Name.anonymous, ([] : List Name))
  for cmd in commands do
    if cmd.isOfKind ``Lean.Parser.Command.declaration then
      if let some short := declIdName? cmd then
        if state.1 ++ short == wanted then
          let some range := cmd.getRange? | return .error s!"`{declName}` has no source range"
          return .ok (wholeLines source range, state.1)
    state := scopeStep state cmd
  return .error s!"no declaration named `{declName}` in this file"

/-- Where to splice a declaration whose namespace is `ns`: after the LAST command of the target that
    sits in exactly that namespace, so the surrounding `namespace`/`end` already match and the
    arrival is in scope for nothing that precedes it.  `none` if the target never opens `ns`.

    Scope commands are skipped, not just tested: `end ns` is itself reached with `ns` still open, so
    counting it puts the declaration one line PAST the `end` — at the root namespace, where it
    elaborates perfectly well under the wrong name and only fails at its call sites. -/
private def insertionPoint? (commands : Array Syntax) (ns : Name) : Option String.Pos.Raw := Id.run do
  let mut state := (Name.anonymous, ([] : List Name))
  let mut best := none
  for cmd in commands do
    let isScope := cmd.isOfKind ``Lean.Parser.Command.namespace ||
      cmd.isOfKind ``Lean.Parser.Command.section || cmd.isOfKind ``Lean.Parser.Command.end
    if state.1 == ns && !isScope then
      if let some tail := cmd.getTailPos? then best := some tail
    else if state.1 == ns && cmd.isOfKind ``Lean.Parser.Command.end then
      -- An otherwise empty namespace still has a legal insertion point: immediately before its
      -- matching `end`.  Using the start (not tail) keeps the declaration inside the namespace.
      if let some start := cmd.getPos?.orElse fun _ => cmd.getRange?.map (·.start) then
        best := some start
    state := scopeStep state cmd
  return best

private def moveDeclaration (sourcePath declName targetPath : String) (apply : Bool) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let (source, _, sourceCommands, _) ← elaborateFile sourcePath
  let ((start, stop), ns) ← match declarationSite source sourceCommands declName with
    | .ok site => pure site
    | .error message => IO.eprintln s!"{sourcePath}: {message}"; return 1
  let text := (String.Pos.Raw.extract source start stop).trimAscii.toString
  let (target, _, targetCommands, _) ← elaborateFile targetPath
  let some anchor := insertionPoint? targetCommands ns
    | IO.eprintln s!"{targetPath}: never opens namespace `{ns}`, so `{declName}` has nowhere to land"
      IO.eprintln "parsed top-level command syntax:"
      for cmd in targetCommands do
        IO.eprintln s!"  {cmd.getKind}: {repr cmd}"
      return 1
  let newSource := applyEdits source #[{ start, stop, line := 0 }]
  let newTarget := applyEdits target #[{ start := anchor, stop := anchor, line := 0,
                                         replacement := "\n\n" ++ text ++ "\n" }]
  IO.println s!"move `{declName}` ({text.length} bytes, namespace `{ns}`)"
  IO.println s!"  from {sourcePath}  to {targetPath}"
  unless apply do IO.println "preview only; pass --apply to write"; return 0
  IO.FS.writeFile targetPath newTarget
  IO.FS.writeFile sourcePath newSource
  let restore : IO Unit := do
    IO.FS.writeFile targetPath target; IO.FS.writeFile sourcePath source
  -- The declaration may have leaned on `variable`s of the section it is leaving, or on dependencies
  -- the target cannot reach; both surface here, in one cheap elaboration, before any build.
  let targetCheck ← IO.Process.output {
    cmd := "./scripts/cap", args := #["lake", "env", "lean", targetPath] }
  unless targetCheck.exitCode == 0 do
    restore
    unless targetCheck.stdout.isEmpty do IO.eprintln targetCheck.stdout
    unless targetCheck.stderr.isEmpty do IO.eprintln targetCheck.stderr
    IO.eprintln (s!"{targetPath} does not elaborate with `{declName}` added (it needs `variable`s " ++
      "or dependencies not available there); both files restored")
    return 1
  -- The SOURCE cannot be checked in-process: it now resolves the declaration through the target's
  -- `.olean`, which is still the pre-move one until the target is recompiled.  So the gate for that
  -- side is a real build, as for binder removal.
  IO.println "verifying the repository after the move..."
  let build ← repositoryBuild
  if build.exitCode == 0 then
    IO.println s!"whole-repository build passed; `{declName}` now lives in {targetPath}"
    return 0
  restore
  IO.eprintln build.stdout
  IO.eprintln s!"whole-repository build failed after moving `{declName}`; both files restored"
  return 1

/-! ## Collapsing a duplicate declaration

`collapse` replaces every syntax-resolved use of a declaration in its own file, removes the
declaration (including its docstring), and retains the transaction only when the file and capped
repository build pass.  Walking identifier syntax in addition to `.ilean` references is essential:
tactic arguments such as `unfold foo` are resolved by Lean but absent from the reference data. -/

private partial def syntaxContainsIdent (wanted : String) (stx : Syntax) : Bool :=
  (stx.isIdent && stx.getId.toString == wanted) ||
    stx.getArgs.any (syntaxContainsIdent wanted)

private partial def identifierEditsNamed (source : String) (fileMap : FileMap)
    (declName replacement : String) (stx : Syntax) (dropAsDuplicate := false) : Array Edit := Id.run do
  let mut found := #[]
  let shortName := (declName.splitOn ".").getLastD declName
  if stx.isIdent && (stx.getId.toString == declName || stx.getId.toString == shortName) then
    if let some range := stx.getRange? then
      let start := if dropAsDuplicate then Id.run do
        let mut p := range.start
        while p.byteIdx > 0 do
          let previous := p.unoffsetBy ⟨1⟩
          let char := String.Pos.Raw.extract source previous p
          if char == " " || char == "\t" then p := previous else break
        return p
      else range.start
      found := found.push {
        start, stop := range.stop
        line := (fileMap.toPosition range.start).line + 1
        replacement := if dropAsDuplicate then "" else replacement
      }
  let childIsDuplicate := dropAsDuplicate ||
    (stx.isOfKind ``Lean.Parser.Tactic.unfold && syntaxContainsIdent replacement stx)
  for child in stx.getArgs do
    found := found ++ identifierEditsNamed source fileMap declName replacement child childIsDuplicate
  return found

private def collapseDeclaration (path declName replacement : String) (apply : Bool) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let (source, fileMap, commands, _) ← elaborateFile path
  let ((declStart, declStop), _) ← match declarationSite source commands declName with
    | .ok site => pure site
    | .error message => IO.eprintln s!"{path}: {message}"; return 1
  let mut candidateEdits := #[{ start := declStart, stop := declStop, line := 0 }]
  for cmd in commands do
    for edit in identifierEditsNamed source fileMap declName replacement cmd do
      -- Exclude the declaration being deleted, including its binding identifier and body.
      unless declStart ≤ edit.start && edit.stop ≤ declStop do
        candidateEdits := candidateEdits.push edit
  let (selectedEdits, deferred) := independentEdits candidateEdits
  if deferred != 0 then
    IO.eprintln s!"{path}: refusing {deferred} overlapping collapse edit(s)"
    return 1
  IO.println s!"collapse `{declName}` into `{replacement}` in {path}: {selectedEdits.size - 1} use(s)"
  for edit in selectedEdits do
    if edit.line != 0 then IO.println s!"  line {edit.line}"
  unless apply do IO.println "preview only; pass --apply to write"; return 0
  let updated := applyEdits source selectedEdits
  IO.FS.writeFile path updated
  unless ← fileElaboratesCleanly path updated do
    IO.FS.writeFile path source
    IO.eprintln s!"{path}: collapsed source does not elaborate; restored"
    return 1
  IO.println "verifying the capped repository build after the collapse..."
  let build ← repositoryBuild
  if build.exitCode == 0 then
    IO.println s!"whole-repository build passed; removed `{declName}`"
    return 0
  IO.FS.writeFile path source
  unless build.stdout.isEmpty do IO.eprintln build.stdout
  unless build.stderr.isEmpty do IO.eprintln build.stderr
  IO.eprintln s!"whole-repository build failed after collapsing `{declName}`; restored"
  return 1

/-- Does `line` use `name` as a standalone identifier (not as part of a longer one)? -/
private def isIdentifierUse (line name : String) : Bool := Id.run do
  let isPart (c : Char) := c.isAlphanum || c == '_' || c == '\'' || c == '.'
  let chars := line.toList
  let target := name.toList
  let mut rest := chars
  let mut previous : Option Char := none
  while !rest.isEmpty do
    if rest.take target.length == target then
      let after := rest.drop target.length
      if !previous.any isPart && !(after.head?.any isPart) then return true
    previous := rest.head?
    rest := rest.drop 1
  return false

/-- Rewrite every reference to `declName` in `path` to `replacement`, resolved semantically: the
    `.ilean` reference data first, then this module's own info trees, and only then identifier
    syntax.  The declaration's own binding site is left alone — renaming a use is not renaming a
    definition, and the two are different edits. -/
private def renameReferences (path moduleName declName replacement : String) (apply : Bool) :
    IO UInt32 := do
  claimElaboration path
  initSearchPath (← findSysroot)
  let source ← IO.FS.readFile path
  let inputCtx := Parser.mkInputContext source path
  let (header, parserState, headerMessages) ← Parser.parseHeader inputCtx
  let (env, headerMessages) ← Elab.processHeader header {} headerMessages inputCtx
    (mainModule := parseName moduleName)
  unless !headerMessages.hasErrors do
    for msg in headerMessages.toList do IO.eprintln (← msg.toString)
    return 1
  let frontend ← Elab.IO.processCommands inputCtx parserState (Elab.Command.mkState env {} {})
  let references := Server.findModuleRefs inputCtx.fileMap
    frontend.commandState.infoState.trees.toArray (localVars := false)
  let (liveReferences, _) ← references.toLspModuleRefs
  let mut sites := usageSitesNamed liveReferences declName
  if sites.isEmpty then
    for cmd in frontend.commands do
      sites := sites ++ syntaxSitesNamed inputCtx.fileMap declName cmd
  if sites.isEmpty then IO.println s!"{path}: no reference to `{declName}`"; return 0
  let edits := sites.map fun site =>
    { start := inputCtx.fileMap.lspPosToUtf8Pos site.range.start,
      stop := inputCtx.fileMap.lspPosToUtf8Pos site.range.end,
      line := site.range.start.line + 1, replacement }
  for edit in edits do
    IO.println s!"{path}:{edit.line}: {repr (String.Pos.Raw.extract source edit.start edit.stop)} -> {repr replacement}"
  unless apply do IO.println "preview only; pass --apply to write"; return 0
  let updated := applyEdits source (independentEdits edits).1
  IO.FS.writeFile path updated
  unless ← elaboratesCleanly env path updated do
    IO.FS.writeFile path source
    IO.eprintln s!"{path}: rewriting `{declName}` to `{replacement}` does not elaborate; restored"
    return 1
  IO.println s!"applied {edits.size} rename(s) to {path}"
  -- The info trees do not record EVERY occurrence — `unfold`'s arguments, among others, resolve
  -- without leaving a term reference — so a semantic pass can silently half-rename a file and only
  -- break once the old declaration is deleted.  Say so rather than report a clean run.
  let short := (declName.splitOn ".").getLastD declName
  let leftovers := (updated.splitOn "\n").zipIdx.filterMap fun (line, i) =>
    if isIdentifierUse line short then some (i + 1) else none
  unless leftovers.isEmpty do
    IO.eprintln s!"{path}: `{short}` still occurs on line(s) {leftovers} — the info trees did not"
    IO.eprintln "  resolve those; check them by hand before deleting the declaration"
  return 0

/-- Run one `lean-refactor` subcommand per matching file, each in a CHILD process.

    Elaborating a file retains its whole `Environment`, so looping over a glob IN-PROCESS
    accumulates one environment per file.  Measured: a `rename --glob 'Freyd/*.lean'` over 200+
    modules reached 18.3 GB resident and was OOM-killed.  A child per file hands the memory back at
    every step, and one file's failure no longer takes the run down. -/
private def forkPerFile (pattern : String) (childArgs : String → Array String) : IO UInt32 := do
  let selected ← globSelectedFiles pattern
  if selected.isEmpty then return 1
  let mut status : UInt32 := 0
  for path in selected do
    let output ← IO.Process.output { cmd := "lake", args := #["exe", "lean-refactor"] ++ childArgs path }
    unless output.stdout.isEmpty do IO.print output.stdout
    unless output.stderr.isEmpty do IO.eprint output.stderr
    if output.exitCode != 0 then status := output.exitCode
  return status

private def renameGlob (pattern declName replacement : String) (apply : Bool) : IO UInt32 :=
  forkPerFile pattern fun path =>
    #["rename-file", path, declName, replacement] ++ (if apply then #["--apply"] else #[])

/-! ## Token renaming (syntax-atom-anchored, for notation)

`rename-token` rewrites a notation token (like `⊆c` → `⊆ₛ`) by walking the elaborated command
syntax tree and replacing every `Syntax.atom` node whose value matches `<old-token>`.  Because it
operates on the parse tree, it never touches a token inside a docstring, comment or string literal —
those are not atom nodes.  The file is elaborated first so that the repo's own custom notation
parses correctly. -/

private partial def renameTokenAtoms (stx : Syntax) (oldToken newToken : String)
    (fileMap : FileMap) : Array Edit := Id.run do
  let mut edits := #[]
  for child in stx.getArgs do
    edits := edits ++ renameTokenAtoms child oldToken newToken fileMap
  match stx with
  | .atom _ val =>
    if val.trimAscii.toString == oldToken then
      if let some range := stx.getRange? then
        let ln := (fileMap.toPosition range.start).line + 1
        edits := edits.push { start := range.start, stop := range.stop, line := ln, replacement := newToken }
  | _ => pure ()
  return edits

private def renameTokenFile (path oldToken newToken : String) (apply : Bool) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let (source, fileMap, commands, _) ← elaborateFile path
  let mut edits := #[]
  for cmd in commands do
    edits := edits ++ renameTokenAtoms cmd oldToken newToken fileMap
  if edits.isEmpty then
    IO.println s!"{path}: no atom `{oldToken}` in parse tree"
    return 0
  let (selected, deferred) := independentEdits edits
  if deferred > 0 then
    IO.println s!"deferred {deferred} overlapping token edit(s)"
  for edit in selected do
    let old := String.Pos.Raw.extract source edit.start edit.stop
    IO.println s!"{path}:{edit.line}: {repr old} -> {repr newToken}"
  unless apply do IO.println "preview only; pass --apply to write"; return 0
  let updated := applyEdits source selected
  IO.FS.writeFile path updated
  unless ← fileElaboratesCleanly path updated do
    IO.FS.writeFile path source
    IO.eprintln s!"{path}: token rename does not elaborate; restored"
    return 1
  IO.println s!"applied {selected.size} token rename(s) to {path}"
  return 0

private def renameTokenGlob (pattern oldToken newToken : String) (apply : Bool) : IO UInt32 :=
  forkPerFile pattern fun path =>
    #["rename-token", path, oldToken, newToken] ++ (if apply then #["--apply"] else #[])

private def refactorSuggestedWarnings (selector : WarningSelector) (apply : Bool)
    (tryRemoval := false) (includeVariables := true) : IO UInt32 := do
  claimElaboration selector.path
  let moduleName ← match moduleNameOfPath selector.path with
    | .ok name => pure name
    | .error message => IO.eprintln message; return 2
  let source ← IO.FS.readFile selector.path
  let inputCtx := Parser.mkInputContext source selector.path
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
  let ileanPath := System.FilePath.mk ".lake/build/lib/lean" /
    System.FilePath.mk (moduleName.replace "." "/" ++ ".ilean")
  -- Reference data is consulted only when we actually delete a binder (the removal path); the default
  -- underscore fix needs none.  Load it best-effort so a missing `.ilean` never aborts a glob run.
  let ilean? ← if includeVariables && tryRemoval then do
      try pure (some (← Ilean.load ileanPath)) catch _ => pure none
    else pure none
  let commands := frontend.commands
  let mut edits := #[]
  let mut simpLines : Array Nat := #[]
  let mut selectedWarning := selector.line?.isNone
  for msg in frontend.commandState.messages.toList do
    let rendered := toString (← msg.data.format)
    if msg.severity == .warning && rendered.contains "unused" then
      let matchesPosition := match selector.line?, selector.column? with
        | some line, some column => msg.pos.line == line && msg.pos.column == column
        | some line, none => msg.pos.line == line
        | none, _ => true
      if matchesPosition then
        selectedWarning := true
        let hintEdits ← messageHintEdits msg.data inputCtx.fileMap
        if !hintEdits.isEmpty then
          edits := edits ++ hintEdits
        else match (if includeVariables then unusedBinderName? rendered else none) with
          | some binderName =>
            match unusedVariableEdits source inputCtx.fileMap commands ilean? moduleName binderName msg.pos tryRemoval with
            | .ok binderEdits => edits := edits ++ binderEdits
            | .error error => IO.eprintln s!"{selector.path}:{msg.pos.line}:{msg.pos.column}: {error}"
          | none =>
            -- e.g. "This simp argument is unused": the fix is a Lean code action stored in the info
            -- tree, gathered from `tryThisEdits` below for exactly the lines we flagged here.
            simpLines := simpLines.push msg.pos.line
  unless selectedWarning do
    IO.eprintln s!"no unused warning at {selector.path}:{selector.line?.getD 0}:{selector.column?.getD 0}"
    return 1
  let availableEdits := tryThisEdits frontend inputCtx.fileMap
  edits := edits ++ availableEdits.filter fun edit => simpLines.contains edit.line
  let (selectedEdits, deferred) := independentEdits edits
  for edit in selectedEdits do
    let old := String.Pos.Raw.extract source edit.start edit.stop
    IO.println s!"{selector.path}:{edit.line}: replace {repr old} with {repr edit.replacement}"
  if selectedEdits.isEmpty then
    IO.println (s!"{selector.path}: selected warning(s) have no matching Lean code-action edit " ++
      s!"({availableEdits.size} code action(s) found)")
  else
    if deferred > 0 then
      IO.println s!"deferred {deferred} overlapping edit(s) until the next elaboration pass"
    if apply then
      let verified ← verifiedEdits env selector.path source selectedEdits
      if verified.isEmpty then
        IO.eprintln (s!"{selector.path}: every candidate edit introduces an elaboration error " ++
          "(linter false positive or a name-referenced parameter); leaving the file unchanged")
      else
        IO.FS.writeFile selector.path (applyEdits source verified)
        let skipped := selectedEdits.size - verified.size
        if skipped == 0 then
          IO.println s!"applied {verified.size} edit(s) to {selector.path}"
        else
          IO.println (s!"applied {verified.size} of {selectedEdits.size} edit(s) to {selector.path}; " ++
            s!"skipped {skipped} that would not elaborate")
  pure 0

private partial def refactorSuggestedWarningsUntilStable
    (selector : WarningSelector) (fuel : Nat := 100) : IO UInt32 := do
  if fuel == 0 then
    IO.eprintln s!"refusing: warning refactoring did not stabilize for {selector.path}"
    return 1
  let before ← IO.FS.readFile selector.path
  let status ← refactorSuggestedWarnings selector true
  if status != 0 then return status
  let after ← IO.FS.readFile selector.path
  if before == after then return 0
  refactorSuggestedWarningsUntilStable selector (fuel - 1)

private def transactionalWarningRefactor (selector : WarningSelector) : IO UInt32 := do
  let original ← IO.FS.readFile selector.path
  let status ← refactorSuggestedWarnings selector true (tryRemoval := true)
  if status != 0 then return status
  let candidate ← IO.FS.readFile selector.path
  if candidate == original then return 0
  IO.println "verifying complete repository after removing the binder..."
  let removalBuild ← repositoryBuild
  if removalBuild.exitCode == 0 then
    IO.println "whole-repository build passed; retained binder removal"
    return 0
  IO.FS.writeFile selector.path original
  IO.println "whole-repository build failed; restored removal candidate and applying anonymous `_` fallback"
  let fallbackStatus ← refactorSuggestedWarnings selector true
  if fallbackStatus != 0 then return fallbackStatus
  let fallbackBuild ← repositoryBuild
  if fallbackBuild.exitCode != 0 then
    IO.FS.writeFile selector.path original
    IO.eprintln fallbackBuild.stderr
    IO.eprintln "anonymous fallback also failed; restored original source"
    return 1
  IO.println "whole-repository build passed with anonymous `_`; removal is not type-correct in the repository"
  return 0

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
  "usage:\n  lean-refactor move <source.lean> <full-declaration-name> <target.lean> [--apply]\n  lean-refactor collapse <source.lean> <full-declaration-name> <replacement> [--apply]\n  lean-refactor rename <source.lean> <module> <full-declaration-name> <replacement> [--apply]\n  lean-refactor rename --glob '<pattern>' <full-declaration-name> <replacement> [--apply]\n  lean-refactor rename-file <source.lean> <full-declaration-name> <replacement> [--apply]\n  lean-refactor rename-token <source.lean> <old-token> <new-token> [--apply]\n  lean-refactor rename-token --glob '<pattern>' <old-token> <new-token> [--apply]\n  lean-refactor unused <source.lean>:<line>:<column> [--apply]\n  lean-refactor unused --glob '<pattern>' [--apply]\n  lean-refactor unused-simp --glob '<pattern>' [--apply]\n  lean-refactor inspect <source.lean> <module> <declaration-module> <full-declaration-name>\n  lean-refactor remove-call-arg <source.lean> <module> <declaration-module> <full-declaration-name> <1-based-index> [--apply]\n  lean-refactor insert-call-arg <source.lean> <module> <declaration-module> <full-declaration-name> <before-1-based-index> <term> [--apply]\n  lean-refactor remove-parameter <source.lean> <module> <full-declaration-name> <binder-name> <1-based-index> [--apply]"

def main (args : List String) : IO UInt32 := do
  match args with
  | ["move", sourcePath, declName, targetPath] =>
      return ← moveDeclaration sourcePath declName targetPath false
  | ["move", sourcePath, declName, targetPath, "--apply"] =>
      return ← moveDeclaration sourcePath declName targetPath true
  | ["collapse", sourcePath, declName, replacement] =>
      return ← collapseDeclaration sourcePath declName replacement false
  | ["collapse", sourcePath, declName, replacement, "--apply"] =>
      return ← collapseDeclaration sourcePath declName replacement true
  | ["rename-file", path, declName, replacement] | ["rename-file", path, declName, replacement, "--apply"] =>
      let moduleName ← match moduleNameOfPath path with
        | .ok n => pure n
        | .error message => IO.eprintln message; return 2
      return ← renameReferences path moduleName declName replacement
        (args.getLast? == some "--apply")
  | ["rename", "--glob", pattern, declName, replacement] =>
      return ← renameGlob pattern declName replacement false
  | ["rename", "--glob", pattern, declName, replacement, "--apply"] =>
      return ← renameGlob pattern declName replacement true
  | ["rename", path, moduleName, declName, replacement] =>
      return ← renameReferences path moduleName declName replacement false
  | ["rename", path, moduleName, declName, replacement, "--apply"] =>
      return ← renameReferences path moduleName declName replacement true
  | ["rename-token", "--glob", pattern, oldToken, newToken] =>
      return ← renameTokenGlob pattern oldToken newToken false
  | ["rename-token", "--glob", pattern, oldToken, newToken, "--apply"] =>
      return ← renameTokenGlob pattern oldToken newToken true
  | ["rename-token", path, oldToken, newToken] =>
      return ← renameTokenFile path oldToken newToken false
  | ["rename-token", path, oldToken, newToken, "--apply"] =>
      return ← renameTokenFile path oldToken newToken true
  | ["unused", selector] | ["unused", selector, "--apply"] =>
      let parsed ← match parseWarningSelector selector with
        | .ok parsed => pure parsed
        | .error message => IO.eprintln message; return 2
      if args.getLast? == some "--apply" then
        return ← transactionalWarningRefactor parsed
      return ← refactorSuggestedWarnings parsed false
  | ["unused", "--glob", pattern] | ["unused", "--glob", pattern, "--apply"] =>
      let apply := args.getLast? == some "--apply"
      let selected ← globSelectedFiles pattern
      if selected.isEmpty then return 1
      let mut status := 0
      for path in selected do
        let code ← if apply then refactorSuggestedWarningsUntilStable { path }
          else refactorSuggestedWarnings { path } false
        if code != 0 then status := code
      return status
  | ["unused-simp-file", path] | ["unused-simp-file", path, "--apply"] =>
      return ← refactorSuggestedWarnings { path } (args.getLast? == some "--apply")
        (includeVariables := false)
  | ["unused-simp", "--glob", pattern] | ["unused-simp", "--glob", pattern, "--apply"] =>
      let apply := args.getLast? == some "--apply"
      return ← forkPerFile pattern fun path =>
        #["unused-simp-file", path] ++ (if apply then #["--apply"] else #[])
  | _ => pure ()
  let (mode, sourcePath, moduleName, declModule, declName, binderName?, argIndex?, insertText?, apply) ← match args with
    | ["inspect", sourcePath, moduleName, declModule, declName] =>
        pure ("inspect", sourcePath, moduleName, declModule, declName, none, none, none, false)
    | ["remove-call-arg", sourcePath, moduleName, declModule, declName, index] =>
        pure ("remove", sourcePath, moduleName, declModule, declName, none, index.toNat?, none, false)
    | ["remove-call-arg", sourcePath, moduleName, declModule, declName, index, "--apply"] =>
        pure ("remove", sourcePath, moduleName, declModule, declName, none, index.toNat?, none, true)
    | ["insert-call-arg", sourcePath, moduleName, declModule, declName, index, term] =>
        pure ("insert", sourcePath, moduleName, declModule, declName, none, index.toNat?, some term, false)
    | ["insert-call-arg", sourcePath, moduleName, declModule, declName, index, term, "--apply"] =>
        pure ("insert", sourcePath, moduleName, declModule, declName, none, index.toNat?, some term, true)
    | ["remove-parameter", sourcePath, moduleName, declName, binderName, index] =>
        pure ("parameter", sourcePath, moduleName, moduleName, declName, some binderName, index.toNat?, none, false)
    | ["remove-parameter", sourcePath, moduleName, declName, binderName, index, "--apply"] =>
        pure ("parameter", sourcePath, moduleName, moduleName, declName, some binderName, index.toNat?, none, true)
    | _ => IO.eprintln usage; return 2
  claimElaboration sourcePath
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
    if mode != "remove" && mode != "insert" then
      for msg in frontend.commandState.messages.toList do IO.eprintln (← msg.toString)
      return 1
  let commands := frontend.commands
  let ileanPath := System.FilePath.mk ".lake/build/lib/lean" /
    System.FilePath.mk (moduleName.replace "." "/" ++ ".ilean")
  let ilean ← Ilean.load ileanPath
  let mut sites := usageSites ilean declModule declName
  if sites.isEmpty && (mode == "remove" || mode == "insert") then
    let refs := Server.findModuleRefs inputCtx.fileMap
      frontend.commandState.infoState.trees.toArray (localVars := false)
    let (liveReferences, _) ← refs.toLspModuleRefs
    sites := usageSitesIn liveReferences declModule declName
    if sites.isEmpty then sites := usageSitesNamed liveReferences declName
    if sites.isEmpty && env.contains (parseName declName) then
      for command in frontend.commands do
        sites := sites ++ syntaxSitesNamed inputCtx.fileMap declName command
  IO.println s!"{declName}: {sites.size} resolved use(s) in {moduleName}; parsed {commands.size} command(s)"
  if mode == "inspect" then
    for site in sites do showContext inputCtx.fileMap site commands
  else
    let some oneBased := argIndex? | IO.eprintln "argument index must be a positive integer"; return 2
    if oneBased == 0 then IO.eprintln "argument index is 1-based"; return 2
    let mut edits := #[]
    for site in sites do
      let result := if mode == "insert" then
        insertionForSite inputCtx.fileMap site commands (oneBased - 1) (insertText?.getD "")
      else editForSite inputCtx.fileMap site commands (oneBased - 1)
      match result with
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
