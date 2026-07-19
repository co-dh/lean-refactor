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
    (ilean : Ilean) (moduleName binderName : String) (warningPos : Position) : Except String (Array Edit) := do
  let pos := fileMap.ofPosition warningPos
  let some (ident, parents) := commands.findSome? (syntaxAt pos)
    | throw "unused warning has no original syntax node"
  unless ident.isIdent && ident.getId.toString == binderName do
    throw s!"unused warning does not point at binder `{binderName}`"
  let binder? := parents.find? fun parent =>
    parent.isOfKind ``Lean.Parser.Term.explicitBinder ||
    parent.isOfKind ``Lean.Parser.Term.implicitBinder ||
    parent.isOfKind ``Lean.Parser.Term.instBinder
  let some binder := binder? | do
    let some range := ident.getRange? | throw "unused positional binder has no source range"
    return #[{ start := range.start, stop := range.stop, line := warningPos.line, replacement := "_" }]
  let isTopLevelParameter :=
    parents.any (·.isOfKind ``Lean.Parser.Command.declSig) &&
      !parents.any (·.isOfKind ``Lean.Parser.Term.forall)
  unless isTopLevelParameter do
    let some range := ident.getRange? | throw "nested binder identifier has no source range"
    return #[{ start := range.start, stop := range.stop, line := warningPos.line, replacement := "_" }]
  let binderRemoval ← binderEditAt source fileMap binder ident
  unless binder.isOfKind ``Lean.Parser.Term.explicitBinder do return #[binderRemoval]
  let some declaration := parents.find? (·.isOfKind ``Lean.Parser.Command.declaration)
    | throw "explicit unused binder is not inside a declaration"
  let (some argumentIndex, _) := explicitBinderIndexAt pos declaration
    | do
      let some range := ident.getRange? | throw "nested binder identifier has no source range"
      return #[{ start := range.start, stop := range.stop, line := warningPos.line, replacement := "_" }]
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
    if ← entry.path.isDir then
      files := files ++ (← leanFilesUnder entry.path)
    else if entry.path.extension == some "lean" then
      files := files.push entry.path.toString
  pure files

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

private def refactorSuggestedWarnings (selector : WarningSelector) (apply : Bool) : IO UInt32 := do
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
  let ilean ← Ilean.load ileanPath
  let commands := frontend.commands
  let mut edits := #[]
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
        else if let some binderName := unusedBinderName? rendered then
          match unusedVariableEdits source inputCtx.fileMap commands ilean moduleName binderName msg.pos with
          | .ok binderEdits => edits := edits ++ binderEdits
          | .error error => IO.eprintln s!"{selector.path}:{msg.pos.line}:{msg.pos.column}: {error}"
  unless selectedWarning do
    IO.eprintln s!"no unused warning at {selector.path}:{selector.line?.getD 0}:{selector.column?.getD 0}"
    return 1
  let availableEdits := tryThisEdits frontend inputCtx.fileMap
  if edits.isEmpty then
    edits := availableEdits.filter fun edit => selector.line?.all fun line => line == edit.line
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
      IO.FS.writeFile selector.path (applyEdits source selectedEdits)
      IO.println s!"applied {selectedEdits.size} edit(s) to {selector.path}"
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
  "usage:\n  lean-refactor unused <source.lean>:<line>:<column> [--apply]\n  lean-refactor unused --glob '<pattern>' [--apply]\n  lean-refactor inspect <source.lean> <module> <declaration-module> <full-declaration-name>\n  lean-refactor remove-call-arg <source.lean> <module> <declaration-module> <full-declaration-name> <1-based-index> [--apply]\n  lean-refactor insert-call-arg <source.lean> <module> <declaration-module> <full-declaration-name> <before-1-based-index> <term> [--apply]\n  lean-refactor remove-parameter <source.lean> <module> <full-declaration-name> <binder-name> <1-based-index> [--apply]"

def main (args : List String) : IO UInt32 := do
  match args with
  | ["unused", selector] | ["unused", selector, "--apply"] =>
      let parsed ← match parseWarningSelector selector with
        | .ok parsed => pure parsed
        | .error message => IO.eprintln message; return 2
      return ← refactorSuggestedWarnings parsed (args.getLast? == some "--apply")
  | ["unused", "--glob", pattern] | ["unused", "--glob", pattern, "--apply"] =>
      let apply := args.getLast? == some "--apply"
      let files ← leanFilesUnder "."
      let selected := files.map (fun path => if path.startsWith "./" then (path.drop 2).toString else path)
        |>.filter (globMatches pattern)
      if selected.isEmpty then IO.eprintln s!"glob matched no Lean files: {pattern}"; return 1
      let mut status := 0
      for path in selected do
        let code ← if apply then refactorSuggestedWarningsUntilStable { path }
          else refactorSuggestedWarnings { path } false
        if code != 0 then status := code
      return status
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
