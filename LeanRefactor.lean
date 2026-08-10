module

import Lean
import LeanRefactor.Fork
import LeanRefactor.Index
import LeanRefactor.Query
import LeanRefactor.SyntaxQuery
import LeanRefactor.SyntaxRows

/-!
`lean-refactor` performs conservative source edits using two pieces of information produced by Lean:

* `.ilean` reference data identifies uses of a particular global declaration semantically;
* the fully elaborated command syntax tree identifies the enclosing application and its explicit arguments.

The tool previews by default and refuses an edit if a resolved reference is not an ordinary application,
the requested argument is absent, or an original source range is unavailable.  It intentionally does not
fall back to textual matching.
-/

open Lean Lean.Parser Lean.Server LeanRefactor.Fork LeanRefactor.SyntaxQuery

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

/-- The last component of a declaration name — what the source actually writes when the enclosing
    namespace is open, and so what every textual pass has to look for. -/
private def shortName (declName : String) : String := (declName.splitOn ".").getLastD declName

/-- Every spelling of `declName` a file may legally write, longest first: the full name and each of
    its component-boundary suffixes.  Inside `namespace Freyd` the source writes `Alg.foo` for
    `Freyd.Alg.foo`, and with `open Freyd.Alg` it writes `foo`; which of the three appears is a fact
    about the file, not about the declaration, so a pass that looks for only the two ends misses the
    middle. -/
private def spellingsOf (declName : String) : List String :=
  let parts := declName.splitOn "."
  (List.range parts.length).map fun i => String.intercalate "." (parts.drop i)

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

/-- The BINDING site of `declName` — where the name is introduced, not where it is used.  A rename
    that moves the uses without this leaves the file naming a declaration that no longer exists; a
    rename that moves this without the uses leaves the uses dangling.  `rename-decl` takes both. -/
private def definitionSitesNamed (references : Lsp.ModuleRefs) (declName : String) : Array ReferenceSite := Id.run do
  let mut sites := #[]
  for (ident, info) in references do
    if let .const _ name := ident then
      if name == declName then
        if let some loc := info.definition? then
          sites := sites.push { range := loc.range, parent? := loc.parentDecl? }
  return sites

private partial def syntaxSitesNamed (fileMap : FileMap) (declName : String) (stx : Syntax) : Array ReferenceSite := Id.run do
  let mut sites := #[]
  if stx.isIdent && (stx.getId.toString == declName || stx.getId.toString == shortName declName) then
    if let some range := stx.getRange? then
      sites := sites.push {
        range := ⟨fileMap.utf8PosToLspPos range.start, fileMap.utf8PosToLspPos range.stop⟩
        parent? := none
      }
  for child in stx.getArgs do sites := sites ++ syntaxSitesNamed fileMap declName child
  return sites

/-- Uses written through NOTATION.  `∇ n` is `CartBicat.«∇» n` after expansion, but the source has
    no identifier to match — the head is an atom the notation declared — so neither the semantic
    passes nor `syntaxSitesNamed` sees it, and a call-argument edit would silently skip every such
    use.  Matching the atom finds them; the enclosing application is then read as usual. -/
private partial def tokenSitesNamed (fileMap : FileMap) (token : String) (stx : Syntax) :
    Array ReferenceSite := Id.run do
  let mut sites := #[]
  for child in stx.getArgs do sites := sites ++ tokenSitesNamed fileMap token child
  match stx with
  | .atom _ val =>
    if val.trimAscii.toString == token then
      if let some range := stx.getRange? then
        sites := sites.push {
          range := ⟨fileMap.utf8PosToLspPos range.start, fileMap.utf8PosToLspPos range.stop⟩
          parent? := none
        }
  | _ => pure ()
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

/-- The `(f a)` that wraps the application, when the parentheses hold nothing else.  Removing an
    application's SOLE argument leaves the parentheses redundant — `(Δ n)` must become `Δ`, not
    `(Δ)` — and only the parent chain can say whether they are there. -/
private def enclosingParen (fileMap : FileMap) (site : ReferenceSite)
    (commands : Array Syntax) (app : Syntax) : Option Syntax := do
  let pos := fileMap.lspPosToUtf8Pos site.range.start
  let (_, parents) ← commands.findSome? (syntaxAt pos)
  let appRange ← app.getRange?
  let paren ← parents.find? fun parent =>
    parent.isOfKind ``Lean.Parser.Term.paren &&
      (parent.getArgs.filter fun child => !child.isAtom && child.getRange?.isSome).size == 1 &&
      (match parent.getArgs[1]?.bind (·.getRange?) with
        | some inner => inner.start == appRange.start && inner.stop == appRange.stop
        | none => false)
  some paren

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
    (commands : Array Syntax) (argIndex : Nat) (source : String) : Except String Edit := do
  let some app := enclosingApp fileMap site commands
    | throw s!"line {site.range.start.line + 1}: resolved reference is not inside an application"
  let some args := appArgs app
    | throw s!"line {site.range.start.line + 1}: unsupported application syntax"
  let some target := args[argIndex]?
    | throw s!"line {site.range.start.line + 1}: application has only {args.size} explicit argument(s)"
  let some targetRange := target.getRange?
    | throw s!"line {site.range.start.line + 1}: argument has no original source range"
  -- The SOLE argument is a different edit from any other: what is left is not an application at
  -- all but the bare function, so the span runs from the end of the function, and the parentheses
  -- that existed only to hold the application go with it.  This is the shape a parameter takes
  -- when it becomes implicit — `Δ n` becomes `Δ`, `(Δ n)` becomes `Δ`.
  if argIndex == 0 && args.size == 1 then
    let some fn := app.getArgs[0]?
      | throw s!"line {site.range.start.line + 1}: application has no function part"
    let some fnRange := fn.getRange?
      | throw s!"line {site.range.start.line + 1}: function part has no source range"
    let fnText := String.Pos.Raw.extract source fnRange.start fnRange.stop
    match enclosingParen fileMap site commands app with
    | some paren =>
      let some parenRange := paren.getRange?
        | throw s!"line {site.range.start.line + 1}: parenthesis has no source range"
      return { start := parenRange.start, stop := parenRange.stop,
               line := site.range.start.line + 1, replacement := fnText }
    | none =>
      return { start := fnRange.stop, stop := targetRange.stop,
               line := site.range.start.line + 1 }
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
    edits := edits.push (← editForSite fileMap site commands argumentIndex source)
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
    if accepted.any fun prior =>
        edit.start == prior.start && edit.stop == prior.stop &&
          edit.replacement == prior.replacement then
      continue
    else if accepted.any fun prior => edit.start < prior.stop && prior.start < edit.stop then
      deferred := deferred + 1
    else
      accepted := accepted.push edit
  return (accepted, deferred)

/-- Ordinary glob semantics: `*` stays inside one path segment, `**` crosses separators.  The
    distinction is what lets a pattern name a directory without swallowing its subdirectories —
    `Freyd/*.lean` is the 226 section files, `Freyd/**.lean` those plus the six deliberately
    un-imported `Freyd/tool` modules, which have no `.olean` and cannot be elaborated at all. -/
private def globMatches (pattern value : String) : Bool :=
  go pattern.toList value.toList
where
  go : List Char → List Char → Bool
    | [], [] => true
    | [], _ => false
    | '*' :: '*' :: ps, cs => go ps cs || match cs with | [] => false | _ :: cs => go ('*' :: '*' :: ps) cs
    | '*' :: ps, cs => go ps cs || match cs with
      | [] => false
      | c :: cs => c != '/' && go ('*' :: ps) cs
    | '?' :: ps, c :: cs => c != '/' && go ps cs
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

/-- Paths under `dir` whose name ends in `suffix`.  Separate from `leanFilesUnder`, which skips
    dot-directories on purpose: this one has to walk INSIDE `.lake` to see build artefacts. -/
private partial def filesEndingIn (dir : System.FilePath) (suffix : String) : IO (Array String) := do
  let mut out := #[]
  for entry in ← dir.readDir do
    if ← entry.path.isDir then out := out ++ (← filesEndingIn entry.path suffix)
    else if entry.fileName.endsWith suffix then out := out.push entry.path.toString
  return out

/-- Whether a source is on the module system.  The keyword stands alone on its own line above the
    imports, so the line test is exact — and it is the same question three callers ask: the pass
    refusing a file it already converted, the same pass refusing to convert a file whose import is
    not converted yet, and the artefact check deciding whether split `.olean` parts belong to it. -/
private def sourceIsModule (source : String) : Bool :=
  (source.splitOn "\n").any (·.trimAsciiStart.toString.startsWith "module")

/-- Repository-relative `.lean` paths matching `pattern`.  Reports and returns empty if none match,
    so every `--glob` subcommand shares one selection rule and one message.

    `mentioning` is the set of texts an edit must rewrite — a declaration's short name, a notation
    token.  A file whose source contains none of them cannot yield a single edit, so scanning it is
    pure waste, and scanning is the ENTIRE cost of a glob run: one file is a full Lean elaboration,
    0.2 s to 5 s.  Measured on this repository: `mono_comp` occurs in 8 of 500 files, so the filter
    is what turns a repository-wide rename from minutes into seconds.  Plain substring containment,
    not `isIdentifierUse`, on purpose — it also covers notation tokens, and being too generous only
    costs a scan that finds nothing, while being too clever would drop a real edit. -/
private def globSelectedFiles (pattern : String) (mentioning : Array String := #[]) :
    IO (Array String) := do
  let files ← leanFilesUnder "."
  -- `*` crosses `/`, so a single pattern cannot name two directories, and a batch that must be
  -- closed under imports rarely fits inside one.  Commas union several patterns; no path holds one.
  let all := (pattern.splitOn ",").map (·.trimAscii.toString)
  -- A `!` pattern subtracts. `Freyd/*.lean,!Freyd/S1_573_PrimRec.lean` is the batch minus one file,
  -- which enumerating the other 217 by hand is not: the exclusion says WHICH file is special and why
  -- a reader should look there, and it survives the next file added to the directory.
  let (excluded, patterns) := all.partition (·.startsWith "!")
  let excludes := excluded.map (·.drop 1 |>.toString)
  let matched := files.map (fun path => if path.startsWith "./" then (path.drop 2).toString else path)
    |>.filter fun path =>
      patterns.any (globMatches · path) && !excludes.any (globMatches · path)
  if matched.isEmpty then
    IO.eprintln s!"glob matched no Lean files: {pattern}"
    return matched
  if mentioning.isEmpty then return matched
  let mut selected := #[]
  for path in matched do
    let source ← IO.FS.readFile path
    if mentioning.any (fun token => source.contains token) then selected := selected.push path
  let wanted := String.intercalate ", " (mentioning.toList.map fun token => s!"`{token}`")
  if selected.isEmpty then
    IO.eprintln s!"no file matching `{pattern}` mentions {wanted}"
  else if selected.size < matched.size then
    IO.println s!"scanning {selected.size} of {matched.size} file(s) matching `{pattern}`; the rest do not mention {wanted}"
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

/-- The check every transactional refactor is measured against.  NO TARGET is named on purpose: the
    package has four lib roots (`Freyd`, `AOP`, `leet`, `rel`) plus `diag`, and `lake build Freyd`
    builds one of them — a rename that broke `diag` was reported as "build passed". -/
private def repositoryBuild : IO IO.Process.Output :=
  IO.Process.output { cmd := "./scripts/cap", args := #["lake", "build"] }

/-! ## Book-aware declaration lints

These checks deliberately live beside the refactors rather than consuming `graph/decls.tsv`.
They inspect the environment produced by elaborating the source file: declaration ownership,
docstrings and result types are therefore Lean's semantic data, not guesses made from rendered TSV
columns.  The glob driver still forks once per file, respecting the environment-retention bound.
-/

private partial def terminalResult (type : Expr) : Expr :=
  match type.consumeMData with
  | .forallE _ _ body _ => terminalResult body
  | .letE _ _ value body _ => terminalResult (body.instantiate1 value)
  | result => result

private def isFunctorResult (type : Expr) : Bool :=
  match (terminalResult type).getAppFn with
  | .const name _ => name.toString == "Freyd.Functor"
  | _ => false

private def hasFunctorRoleSuffix (name : Name) : Bool :=
  let short := name.getString!
  short.endsWith "Functor" || short.endsWith "Embedding" ||
    short.endsWith "Representation"

private def dropSpace : List Char → List Char
  | c :: rest => if c.isWhitespace then dropSpace rest else c :: rest
  | [] => []

private def decimalPrefix (chars : List Char) : Option (Nat × List Char) :=
  let rec go (chars : List Char) (value count : Nat) :=
    match chars with
    | c :: rest =>
        if c.isDigit then go rest (10 * value + (c.toNat - '0'.toNat)) (count + 1)
        else if count == 0 then none else some (value, chars)
    | [] => if count == 0 then none else some (value, [])
  go chars 0 0

private def sectionCitations (text : String) : Array (Nat × Nat) :=
  ((text.splitOn "§").drop 1 |>.filterMap fun tail => do
    let (chapter, rest) ← decimalPrefix (dropSpace tail.toList)
    let '.' :: rest := rest | none
    let (sectionDigits, _) ← decimalPrefix rest
    some (chapter, sectionDigits)).toArray

private def openingBanner (source : String) : String :=
  String.intercalate "\n" <| (source.splitOn "\n").takeWhile fun line =>
    !(line.trimAsciiStart.toString.startsWith "import ")

private def bannerRange (source : String) (chapter : Nat) : Option (Nat × Nat) := do
  let sections := (sectionCitations (openingBanner source)).filter (·.1 == chapter) |>.map (·.2)
  let first ← sections[0]?
  some <| sections.foldl (init := (first, first)) fun (lo, hi) sectionDigits =>
    (min lo sectionDigits, max hi sectionDigits)

/-! ## Renaming a module

`rename-module` changes both a module's repository-relative filename and every Lean `import` that
names it.  Import edits are deliberately line-oriented and exact: after the old module name only
whitespace or a `--` comment is accepted, so docstrings, declaration names, and longer module names
are left alone.

Applying the operation is transactional at repository scale.  The old file and all edited importers
are restored when the capped repository build fails. -/

private def modulePath (moduleName : String) : Except String String := do
  if moduleName.isEmpty then throw "module name must not be empty"
  let parts := moduleName.splitOn "."
  unless parts.all fun part => !part.isEmpty do
    throw s!"invalid module name: {moduleName}"
  pure <| moduleName.replace "." "/" ++ ".lean"

private def renameImportLine (line oldModule newModule : String) : String × Bool :=
  let trimmed := line.trimAscii.toString
  let oldImport := "import " ++ oldModule
  let suffix := (trimmed.drop oldImport.length).trimAscii.toString
  if trimmed.startsWith oldImport && (suffix.isEmpty || suffix.startsWith "--") then
    (line.replace ("import " ++ oldModule) ("import " ++ newModule), true)
  else
    (line, false)

private def renameImports (source oldModule newModule : String) : String × Nat := Id.run do
  let mut changed := 0
  let mut lines := []
  for line in source.splitOn "\n" do
    let (line, didChange) := renameImportLine line oldModule newModule
    if didChange then changed := changed + 1
    lines := line :: lines
  return (String.intercalate "\n" lines.reverse, changed)

private def restoreModuleRename (oldPath newPath : String)
    (backups : Array (String × String)) : IO Unit := do
  if ← System.FilePath.pathExists newPath then
    IO.FS.rename newPath oldPath
  for (path, source) in backups do
    IO.FS.writeFile path source

private def renameModule (oldModule newModule : String) (apply : Bool) : IO UInt32 := do
  let oldPath ← match modulePath oldModule with
    | .ok path => pure path
    | .error message => IO.eprintln message; return 2
  let newPath ← match modulePath newModule with
    | .ok path => pure path
    | .error message => IO.eprintln message; return 2
  if oldPath == newPath then
    IO.eprintln "old and new module names resolve to the same path"
    return 2
  unless ← System.FilePath.pathExists oldPath do
    IO.eprintln s!"module source does not exist: {oldPath}"
    return 1
  if ← System.FilePath.pathExists newPath then
    IO.eprintln s!"refusing to overwrite existing module source: {newPath}"
    return 1
  let files ← leanFilesUnder "."
  let mut changes : Array (String × String × String × Nat) := #[]
  for rawPath in files do
    let path := if rawPath.startsWith "./" then (rawPath.drop 2).toString else rawPath
    let source ← IO.FS.readFile path
    let (updated, count) := renameImports source oldModule newModule
    if count > 0 then changes := changes.push (path, source, updated, count)
  IO.println s!"rename {oldPath} -> {newPath}"
  for (path, _, _, count) in changes do
    IO.println s!"{path}: rewrite {count} import(s): {oldModule} -> {newModule}"
  unless apply do
    IO.println "preview only; pass --apply to write"
    return 0
  let backups := changes.map fun (path, source, _, _) => (path, source)
  try
    for (path, _, updated, _) in changes do IO.FS.writeFile path updated
    IO.FS.rename oldPath newPath
    let build ← repositoryBuild
    unless build.stdout.isEmpty do IO.eprint build.stdout
    unless build.stderr.isEmpty do IO.eprint build.stderr
    if build.exitCode != 0 then
      restoreModuleRename oldPath newPath backups
      IO.eprintln s!"whole-repository build failed after renaming `{oldModule}`; restored"
      return build.exitCode
    IO.println s!"renamed module `{oldModule}` to `{newModule}`; whole-repository build passed"
    return 0
  catch error =>
    restoreModuleRename oldPath newPath backups
    IO.eprintln s!"module rename failed and was restored: {error}"
    return 1

/-! ## Moving a declaration between files

The dedup report (`scripts/dep_dup.py`) flags duplicate groups where no member is importable from all
the others: collapsing those needs the survivor RELOCATED to a module every caller already imports.
That is the one edit the subcommands above cannot express, and the one the skill calls the riskiest
to do by hand, so it is mechanised here: cut the declaration with its docstring, splice it into the
target namespace selected by `move` or explicit `move-into`, and refuse the edit unless BOTH files
still elaborate. -/

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
  pure (source, ctx.fileMap, frontend.commands, frontend.commandState.env)

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
    -- Command wrappers such as `omit [...] in` contain the declaration syntax rather than being
    -- `Command.declaration` themselves.  Search recursively and retain the wrapper's range so
    -- structural operations move the binder-control command together with its declaration.
    if let some short := declIdName? cmd then
      if state.1 ++ short == wanted then
        let some range := cmd.getRange? | return .error s!"`{declName}` has no source range"
        return .ok (wholeLines source range, state.1)
    state := scopeStep state cmd
  return .error s!"no declaration named `{declName}` in this file"

/-- Locate the parsed command that introduces `declName`. -/
private def declarationSyntax (commands : Array Syntax) (declName : String) :
    Except String Syntax := Id.run do
  let wanted := parseName declName
  let mut state := (Name.anonymous, ([] : List Name))
  for cmd in commands do
    if let some short := declIdName? cmd then
      if state.1 ++ short == wanted then return .ok cmd
    state := scopeStep state cmd
  return .error s!"no declaration named `{declName}` in this file"

private partial def firstSyntaxOfKind? (kind : SyntaxNodeKind) (stx : Syntax) : Option Syntax :=
  if stx.isOfKind kind then some stx
  else stx.getArgs.findSome? (firstSyntaxOfKind? kind)

private partial def syntaxHasIdent (name : String) (stx : Syntax) : Bool :=
  (stx.isIdent && stx.getId.toString == name) ||
    stx.getArgs.any (syntaxHasIdent name)

/-- Replace only the parsed term after `:=` in a declaration.  The operation previews by default and
    restores the source after either an elaboration failure or a capped repository-build failure. -/
private def replaceDeclarationBody (path declName replacement : String) (apply : Bool) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let (source, fileMap, commands, _) ← elaborateFile path
  let declaration ← match declarationSyntax commands declName with
    | .ok stx => pure stx
    | .error message => IO.eprintln s!"{path}: {message}"; return 1
  let some declVal := firstSyntaxOfKind? ``Lean.Parser.Command.declValSimple declaration
    | IO.eprintln s!"{path}: `{declName}` has no simple `:=` body"
      return 1
  let some body := declVal.getArgs[1]?
    | IO.eprintln s!"{path}: `{declName}` has a malformed simple body"
      return 1
  let some range := body.getRange?
    | IO.eprintln s!"{path}: `{declName}` body has no source range"
      return 1
  let line := (fileMap.toPosition range.start).line + 1
  let edit : Edit := {
    start := range.start
    stop := range.stop
    line := (fileMap.toPosition range.start).line + 1
    replacement := replacement
  }
  let updated := applyEdits source #[edit]
  IO.println s!"replace body of `{declName}` in {path} (line {line})"
  unless apply do
    IO.println "preview only; pass --apply to write"
    return 0
  IO.FS.writeFile path updated
  let check ← IO.Process.output {
    cmd := "./scripts/cap", args := #["lake", "env", "lean", path] }
  unless check.exitCode == 0 do
    IO.FS.writeFile path source
    unless check.stdout.isEmpty do IO.eprintln check.stdout
    unless check.stderr.isEmpty do IO.eprintln check.stderr
    IO.eprintln s!"{path}: replacement body does not elaborate; restored"
    return 1
  IO.println "verifying the capped repository build after replacing the body..."
  let build ← repositoryBuild
  if build.exitCode == 0 then
    IO.println s!"whole-repository build passed; replaced body of `{declName}`"
    return 0
  IO.FS.writeFile path source
  unless build.stdout.isEmpty do IO.eprintln build.stdout
  unless build.stderr.isEmpty do IO.eprintln build.stderr
  IO.eprintln s!"whole-repository build failed after replacing `{declName}`; restored"
  return 1

/-- Replace one complete parsed declaration command. This is the structural counterpart of
    `replace-body`: it is intended for changing a theorem's statement together with its proof while
    retaining AST-selected boundaries, preview-by-default behavior, and transactional validation. -/
private def replaceDeclaration (path declName replacement : String) (apply : Bool) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let (source, _, commands, _) ← elaborateFile path
  let ((start, stop), _) ← match declarationSite source commands declName with
    | .ok site => pure site
    | .error message => IO.eprintln s!"{path}: {message}"; return 1
  let edit : Edit := { start, stop, line := 0, replacement := replacement.trimAscii.toString ++ "\n" }
  let updated := applyEdits source #[edit]
  IO.println s!"replace declaration `{declName}` in {path}"
  unless apply do
    IO.println "preview only; pass --apply to write"
    return 0
  IO.FS.writeFile path updated
  let check ← IO.Process.output {
    cmd := "./scripts/cap", args := #["lake", "env", "lean", path] }
  unless check.exitCode == 0 do
    IO.FS.writeFile path source
    unless check.stdout.isEmpty do IO.eprintln check.stdout
    unless check.stderr.isEmpty do IO.eprintln check.stderr
    IO.eprintln s!"{path}: replacement declaration does not elaborate; restored"
    return 1
  IO.println "verifying the capped repository build after replacing the declaration..."
  let build ← repositoryBuild
  if build.exitCode == 0 then
    IO.println s!"whole-repository build passed; replaced declaration `{declName}`"
    return 0
  IO.FS.writeFile path source
  unless build.stdout.isEmpty do IO.eprintln build.stdout
  unless build.stderr.isEmpty do IO.eprintln build.stderr
  IO.eprintln s!"whole-repository build failed after replacing `{declName}`; restored"
  return 1

/-- Remove one complete parsed declaration command. Preview by default; on application, restore the
    source if either the edited file or the capped repository build fails. -/
private def removeDeclaration (path declName : String) (apply : Bool) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let (source, _, commands, _) ← elaborateFile path
  let ((start, stop), _) ← match declarationSite source commands declName with
    | .ok site => pure site
    | .error message => IO.eprintln s!"{path}: {message}"; return 1
  let edit : Edit := { start, stop, line := 0, replacement := "" }
  let updated := applyEdits source #[edit]
  IO.println s!"remove declaration `{declName}` from {path}"
  unless apply do
    IO.println "preview only; pass --apply to write"
    return 0
  IO.FS.writeFile path updated
  let check ← IO.Process.output {
    cmd := "./scripts/cap", args := #["lake", "env", "lean", path] }
  unless check.exitCode == 0 do
    IO.FS.writeFile path source
    unless check.stdout.isEmpty do IO.eprintln check.stdout
    unless check.stderr.isEmpty do IO.eprintln check.stderr
    IO.eprintln s!"{path}: declaration removal does not elaborate; restored"
    return 1
  IO.println "verifying the capped repository build after removing the declaration..."
  let build ← repositoryBuild
  if build.exitCode == 0 then
    IO.println s!"whole-repository build passed; removed declaration `{declName}`"
    return 0
  IO.FS.writeFile path source
  unless build.stdout.isEmpty do IO.eprintln build.stdout
  unless build.stderr.isEmpty do IO.eprintln build.stderr
  IO.eprintln s!"whole-repository build failed after removing `{declName}`; restored"
  return 1

/-- Move a declaration within its file to immediately before another declaration in the same
    namespace.  Both boundaries come from parsed command syntax; preview and rollback follow the
    same transaction contract as the other structural operations. -/
private def relocateDeclarationBefore (path declName anchorName : String) (apply : Bool) :
    IO UInt32 := do
  initSearchPath (← findSysroot)
  let (source, _, commands, _) ← elaborateFile path
  let ((start, stop), ns) ← match declarationSite source commands declName with
    | .ok site => pure site
    | .error message => IO.eprintln s!"{path}: {message}"; return 1
  let ((anchorStart, _), anchorNs) ← match declarationSite source commands anchorName with
    | .ok site => pure site
    | .error message => IO.eprintln s!"{path}: {message}"; return 1
  unless ns == anchorNs do
    IO.eprintln s!"{path}: `{declName}` is in `{ns}`, but `{anchorName}` is in `{anchorNs}`"
    return 1
  unless stop ≤ anchorStart || anchorStart < start do
    IO.eprintln s!"{path}: `{declName}` already contains or precedes `{anchorName}`"
    return 1
  let text := String.Pos.Raw.extract source start stop
  let updated := applyEdits source #[
    { start := start, stop := stop, line := 0 },
    { start := anchorStart, stop := anchorStart, line := 0, replacement := text }
  ]
  IO.println s!"relocate `{declName}` before `{anchorName}` in {path}"
  unless apply do
    IO.println "preview only; pass --apply to write"
    return 0
  IO.FS.writeFile path updated
  let check ← IO.Process.output {
    cmd := "./scripts/cap", args := #["lake", "env", "lean", path] }
  unless check.exitCode == 0 do
    IO.FS.writeFile path source
    unless check.stdout.isEmpty do IO.eprintln check.stdout
    unless check.stderr.isEmpty do IO.eprintln check.stderr
    IO.eprintln s!"{path}: relocated source does not elaborate; restored"
    return 1
  IO.println "verifying the capped repository build after relocating the declaration..."
  let build ← repositoryBuild
  if build.exitCode == 0 then
    IO.println s!"whole-repository build passed; relocated `{declName}`"
    return 0
  IO.FS.writeFile path source
  unless build.stdout.isEmpty do IO.eprintln build.stdout
  unless build.stderr.isEmpty do IO.eprintln build.stderr
  IO.eprintln s!"whole-repository build failed after relocating `{declName}`; restored"
  return 1

/-- Locate a named `section` command and the namespace in force immediately before it. -/
private def sectionSite (source : String) (commands : Array Syntax) (sectionName : String) :
    Except String ((String.Pos.Raw × String.Pos.Raw) × Name) := Id.run do
  let mut state := (Name.anonymous, ([] : List Name))
  for cmd in commands do
    if cmd.isOfKind ``Lean.Parser.Command.section then
      if syntaxHasIdent sectionName cmd then
        let some range := cmd.getRange?
          | return .error s!"section `{sectionName}` has no source range"
        return .ok (wholeLines source range, state.1)
    state := scopeStep state cmd
  return .error s!"no section named `{sectionName}` in this file"

private def relocateDeclarationBeforeSection (path declName sectionName : String) (apply : Bool) :
    IO UInt32 := do
  initSearchPath (← findSysroot)
  let (source, _, commands, _) ← elaborateFile path
  let ((start, stop), ns) ← match declarationSite source commands declName with
    | .ok site => pure site
    | .error message => IO.eprintln s!"{path}: {message}"; return 1
  let ((anchorStart, _), anchorNs) ← match sectionSite source commands sectionName with
    | .ok site => pure site
    | .error message => IO.eprintln s!"{path}: {message}"; return 1
  unless ns == anchorNs do
    IO.eprintln s!"{path}: `{declName}` is in `{ns}`, but section `{sectionName}` starts in `{anchorNs}`"
    return 1
  let text := String.Pos.Raw.extract source start stop
  let updated := applyEdits source #[
    { start := start, stop := stop, line := 0 },
    { start := anchorStart, stop := anchorStart, line := 0, replacement := text }
  ]
  IO.println s!"relocate `{declName}` before section `{sectionName}` in {path}"
  unless apply do
    IO.println "preview only; pass --apply to write"
    return 0
  IO.FS.writeFile path updated
  let check ← IO.Process.output {
    cmd := "./scripts/cap", args := #["lake", "env", "lean", path] }
  unless check.exitCode == 0 do
    IO.FS.writeFile path source
    unless check.stdout.isEmpty do IO.eprintln check.stdout
    unless check.stderr.isEmpty do IO.eprintln check.stderr
    IO.eprintln s!"{path}: relocated source does not elaborate; restored"
    return 1
  IO.println "verifying the capped repository build after relocating the declaration..."
  let build ← repositoryBuild
  if build.exitCode == 0 then
    IO.println s!"whole-repository build passed; relocated `{declName}`"
    return 0
  IO.FS.writeFile path source
  unless build.stdout.isEmpty do IO.eprintln build.stdout
  unless build.stderr.isEmpty do IO.eprintln build.stderr
  IO.eprintln s!"whole-repository build failed after relocating `{declName}`; restored"
  return 1

private def sourceDeclarations (fileMap : FileMap) (env : Environment) (commands : Array Syntax) :
    Array (Name × ConstantInfo × Nat) := Id.run do
  let mut declarations := #[]
  let mut state := (Name.anonymous, ([] : List Name))
  for command in commands do
    if command.isOfKind ``Lean.Parser.Command.declaration then
      if let some short := declIdName? command then
        let name := state.1 ++ short
        if let some info := env.find? name then
          if let some range := command.getRange? then
            declarations := declarations.push (name, info, (fileMap.toPosition range.start).line)
    state := scopeStep state command
  return declarations

private def lintBookFile (path : String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let (source, fileMap, commands, env) ← elaborateFile path
  let mut hits := 0
  for (name, info, line) in sourceDeclarations fileMap env commands do
    let ctx : Core.Context := { fileName := path, fileMap }
    let doc ←
      try
        let action : CoreM (Option String) := findDocString? env name
        Prod.fst <$> action.toIO ctx { env }
      catch _ => pure none
    for (chapter, sectionDigits) in (sectionCitations (doc.getD "")).toList.eraseDups do
      if let some (lo, hi) := bannerRange source chapter then
        if sectionDigits < lo || hi < sectionDigits then
          hits := hits + 1
          IO.println s!"{path}:{line}: [section-home] {name}: doc cites §{chapter}.{sectionDigits} outside banner §{chapter}.{lo}–§{chapter}.{hi}"
    if hasFunctorRoleSuffix name && !isFunctorResult info.type then
      hits := hits + 1
      let rendered ←
        try
          let (formatted, _) ← (Meta.MetaM.run' (Meta.ppExpr info.type)).toIO ctx { env }
          pure ((toString formatted).replace "\n" " ")
        catch _ => pure "<type unavailable>"
      IO.println s!"{path}:{line}: [name-vs-type] {name}: role-name suffix but result is not `Functor`: {rendered}"
  return if hits == 0 then 0 else 1

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

private def moveDeclaration (sourcePath declName targetPath : String) (apply : Bool)
    (omitBinders? : Option String := none) (targetNamespace? : Option String := none) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let (source, _, sourceCommands, _) ← elaborateFile sourcePath
  let ((start, stop), ns) ← match declarationSite source sourceCommands declName with
    | .ok site => pure site
    | .error message => IO.eprintln s!"{sourcePath}: {message}"; return 1
  let declarationText := (String.Pos.Raw.extract source start stop).trimAscii.toString
  let text := match omitBinders? with
    | some binders => "omit " ++ binders ++ " in\n" ++ declarationText
    | none => declarationText
  let targetNs := targetNamespace?.map parseName |>.getD ns
  let (target, _, targetCommands, _) ← elaborateFile targetPath
  let some anchor := insertionPoint? targetCommands targetNs
    | IO.eprintln s!"{targetPath}: never opens namespace `{targetNs}`, so `{declName}` has nowhere to land"
      return 1
  let newSource := applyEdits source #[{ start, stop, line := 0 }]
  let newTarget := applyEdits target #[{ start := anchor, stop := anchor, line := 0,
                                         replacement := "\n\n" ++ text ++ "\n" }]
  IO.println s!"move `{declName}` ({text.length} bytes, namespace `{ns}` → `{targetNs}`)"
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
  let identText := if stx.isIdent then stx.getId.toString else ""
  -- Longest spelling first, so the `.suffix` is measured from the one the source actually wrote:
  -- `Freyd.Alg.foo.bar` must drop thirteen characters, not the three of `foo`.
  let suffix? := (spellingsOf declName).findSome? fun spelling =>
    if identText == spelling then some ""
    else if identText.startsWith (spelling ++ ".") then some (identText.drop spelling.length).toString
    else none
  if stx.isIdent && suffix?.isSome then
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
        replacement := if dropAsDuplicate then "" else replacement ++ suffix?.getD ""
      }
  let childIsDuplicate := dropAsDuplicate ||
    (stx.isOfKind ``Lean.Parser.Tactic.unfold && syntaxContainsIdent replacement stx)
  for child in stx.getArgs do
    found := found ++ identifierEditsNamed source fileMap declName replacement child childIsDuplicate
  return found

private def collapseDeclaration (path declName replacement : String) (apply : Bool)
    (dropCallArg? : Option Nat := none) : IO UInt32 := do
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
  if let some argIndex := dropCallArg? then
    if argIndex == 0 then
      IO.eprintln "collapse-drop-call-arg uses a 1-based argument index"
      return 1
    let mut sites := #[]
    for cmd in commands do
      sites := sites ++ syntaxSitesNamed fileMap declName cmd
    for site in sites do
      let pos := fileMap.lspPosToUtf8Pos site.range.start
      unless declStart ≤ pos && pos < declStop do
        let edit ← match editForSite fileMap site commands (argIndex - 1) source with
          | .ok edit => pure edit
          | .error message => IO.eprintln s!"{path}: {message}"; return 1
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
  let check ← IO.Process.output {
    cmd := "./scripts/cap", args := #["lake", "env", "lean", path] }
  unless check.exitCode == 0 do
    IO.FS.writeFile path source
    unless check.stdout.isEmpty do IO.eprintln check.stdout
    unless check.stderr.isEmpty do IO.eprintln check.stderr
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

/-- One declaration to rename, and what to rename it to. -/
private structure Rename where
  declName : String
  replacement : String

private def renameList (renames : Array Rename) : String :=
  String.intercalate ", " (renames.toList.map fun r => s!"`{r.declName}` to `{r.replacement}`")

/-- `<declaration> <replacement> <declaration> <replacement> …`.  Renames are taken as a BATCH
    because scanning is the whole cost: each pair used to mean another elaboration of every file in
    the glob, so `n` renames cost `n` full passes over the repository for one pass worth of work. -/
private def parseRenames : List String → Except String (Array Rename)
  | [] => .error "expected at least one <declaration> <replacement> pair"
  | args => go args #[]
where
  go : List String → Array Rename → Except String (Array Rename)
    | [], acc => .ok acc
    | [unpaired], _ =>
        .error s!"`{unpaired}` has no replacement; renames come in <declaration> <replacement> pairs"
    | declName :: replacement :: rest, acc => go rest (acc.push { declName, replacement })

/-- The batch as `parseRenames` reads it back, for handing it to a child process. -/
private def renameArgs (renames : Array Rename) : Array String := Id.run do
  let mut args := #[]
  for r in renames do args := args ++ #[r.declName, r.replacement]
  return args

/-- Take a trailing `--apply` off a variadic argument tail; every refactor previews without it. -/
private def stripApply (args : List String) : List String × Bool :=
  match args.reverse with
  | "--apply" :: rest => (rest.reverse, true)
  | _ => (args, false)

/-- Everything one elaboration of a file yields that a rename needs.  It is kept as a value so a
    BATCH of renames shares it: the elaboration costs seconds, deriving the sites costs nothing. -/
private structure ScannedFile where
  source : String
  fileMap : FileMap
  commands : Array Syntax
  references : Lsp.ModuleRefs
  /-- The env of the file's IMPORTS, not of the file itself — `elaboratesCleanly` re-elaborates the
      candidate text against it, which the file's own declarations in scope would make impossible. -/
  env : Environment

/-- A reference site spans the WHOLE identifier as written, qualifier included, so replacing it with
    a bare new name deletes the namespace: `CartBicat.cop` became `delta`, which resolves nowhere.
    When the replacement is a simple name, only the last component moves and the writer's chosen
    qualification is kept.  A dotted replacement is taken verbatim — that is a caller asking for a
    different namespace, not for a rename. -/
private def qualifierPreserving (source declName : String) (edit : Edit) : Edit :=
  if (edit.replacement.splitOn ".").length > 1 then edit else
  let parts := (String.Pos.Raw.extract source edit.start edit.stop).splitOn "."
  if parts.length > 1 && parts.getLastD "" == shortName declName then
    { edit with replacement := String.intercalate "." (parts.dropLast ++ [edit.replacement]) }
  else edit

/-- The semantic and syntactic passes both see a site that is both a reference and an identifier,
    so the union has to be taken by position or the same span is reported — and counted — twice. -/
private def dedupeEdits (edits : Array Edit) : Array Edit := Id.run do
  let mut seen : Array Nat := #[]
  let mut kept := #[]
  for edit in edits do
    unless seen.contains edit.start.byteIdx do
      seen := seen.push edit.start.byteIdx
      kept := kept.push edit
  return kept

/-- Elaborate `path` once, keeping what the reference passes read.  Lean's parser is extensible, so
    the file cannot even be parsed without the environment its imports build; that elaboration is the
    cost every rename pays, and `ScannedFile` is what makes one payment serve a whole batch. -/
private def scanFile (path moduleName : String) : IO (Except UInt32 ScannedFile) := do
  claimElaboration path
  initSearchPath (← findSysroot)
  let source ← IO.FS.readFile path
  let inputCtx := Parser.mkInputContext source path
  let (header, parserState, headerMessages) ← Parser.parseHeader inputCtx
  let (env, headerMessages) ← Elab.processHeader header {} headerMessages inputCtx
    (mainModule := parseName moduleName)
  unless !headerMessages.hasErrors do
    for msg in headerMessages.toList do IO.eprintln (← msg.toString)
    return .error 1
  let frontend ← Elab.IO.processCommands inputCtx parserState (Elab.Command.mkState env {} {})
  let references := Server.findModuleRefs inputCtx.fileMap
    frontend.commandState.infoState.trees.toArray (localVars := false)
  let (liveReferences, _) ← references.toLspModuleRefs
  return .ok { source, fileMap := inputCtx.fileMap, commands := frontend.commands,
               references := liveReferences, env }

/-- Every site in `scan` that names `r.declName`, resolved semantically: this module's own info trees
    first, and only then identifier syntax.  `withDefinition` picks which edit is wanted — renaming a
    USE is not renaming a DEFINITION.  `rename` moves the uses only (the binding site is a separate
    edit the caller may not want); `rename-decl` moves both, which is what an actual rename of a
    declaration is. -/
private def renameEdits (scan : ScannedFile) (r : Rename) (withDefinition : Bool) : Array Edit :=
  Id.run do
  let mut sites := usageSitesNamed scan.references r.declName
  if withDefinition then
    sites := sites ++ definitionSitesNamed scan.references r.declName
    -- A `class`/`structure` field is used by the very laws declared beside it, and inside that body
    -- the field is a BINDER reference, not a `.const` — the info trees do not record it.  Without
    -- the syntax pass, renaming a field leaves its own laws naming the old one, so the file no
    -- longer elaborates.  Only `rename-decl` needs this: it is the operation that moves the
    -- binding site, hence the only one for which the declaring body is in scope.
    for cmd in scan.commands do
      sites := sites ++ syntaxSitesNamed scan.fileMap r.declName cmd
  if sites.isEmpty then
    for cmd in scan.commands do
      sites := sites ++ syntaxSitesNamed scan.fileMap r.declName cmd
  let edits := sites.map fun site =>
    { start := scan.fileMap.lspPosToUtf8Pos site.range.start,
      stop := scan.fileMap.lspPosToUtf8Pos site.range.end,
      line := site.range.start.line + 1, replacement := r.replacement }
  return (dedupeEdits edits).map (qualifierPreserving scan.source r.declName)

/-- The same edits `renameEdits` builds, from sites the index already recorded rather than from a
    fresh elaboration.  The tail — position conversion, de-duplication, qualifier preservation —
    is the shared part and must stay identical, or the two paths stop agreeing. -/
private def indexRenameEdits (fileMap : FileMap) (source : String) (r : Rename)
    (sites : Array Query.Site) : Array Edit :=
  (dedupeEdits (sites.map fun site =>
    { start := fileMap.lspPosToUtf8Pos ⟨site.l1, site.c1⟩,
      stop  := fileMap.lspPosToUtf8Pos ⟨site.l2, site.c2⟩,
      line  := site.l1 + 1, replacement := r.replacement })).map (qualifierPreserving source r.declName)

/-- The conflict check every batch of renames must pass.  Two renames can claim the SAME span:
    `syntaxSitesNamed` matches a short name, so `A.bar` and `B.bar` both answer to `bar`.
    Rewriting such a site to one of the two silently would be a wrong edit, so the batch is
    refused and the caller told to run those two renames separately.  Identical claims are just
    the duplicate they look like, and collapse. -/
private def checkedBatch (renames : Array Rename) (editsFor : Rename → Array Edit) :
    Except String (Array Edit) := Id.run do
  let mut kept : Array (Rename × Edit) := #[]
  for r in renames do
    for edit in editsFor r do
      match kept.find? fun (_, other) => other.start == edit.start && other.stop == edit.stop with
      | some (first, other) =>
          if other.replacement != edit.replacement then
            return .error s!"`{first.declName}` and `{r.declName}` both rename the site on line \
              {edit.line}, to `{other.replacement}` and `{edit.replacement}`; run those two \
              renames separately"
      | none => kept := kept.push (r, edit)
  return .ok (kept.map (·.2))

/-- The whole batch's edits for one scanned file, or a refusal: `checkedBatch` over a fresh
    elaboration. -/
private def batchRenameEdits (scan : ScannedFile) (renames : Array Rename) (withDefinition : Bool) :
    Except String (Array Edit) :=
  checkedBatch renames fun r => renameEdits scan r withDefinition

/-- `checkedBatch` over index sites, so a batch the elaboration path refuses is refused here with
    the same message. -/
private def indexBatchRenameEdits (fileMap : FileMap) (source : String) (renames : Array Rename)
    (sitesByDecl : Std.HashMap String (Array Query.Site)) : Except String (Array Edit) :=
  checkedBatch renames fun r => indexRenameEdits fileMap source r (sitesByDecl.getD r.declName #[])

/-- The lines `reportEdits` prints, as data: the index path collects them into the output shape a
    forked child would have produced, so both paths print the identical report. -/
private def reportLines (path source : String) (edits : Array Edit) : Array String :=
  edits.map fun edit =>
    s!"{path}:{edit.line}: {repr (String.Pos.Raw.extract source edit.start edit.stop)} -> {repr edit.replacement}"

private def reportEdits (path source : String) (edits : Array Edit) : IO Unit := do
  for line in reportLines path source edits do IO.println line

/-- The info trees do not record EVERY occurrence — `unfold`'s arguments, among others, resolve
    without leaving a term reference — so a semantic pass can silently half-rename a file and only
    break once the old declaration is deleted.  Say so rather than report a clean run. -/
private def warnLeftovers (path updated declName : String) : IO Unit := do
  let short := shortName declName
  let leftovers := (updated.splitOn "\n").zipIdx.filterMap fun (line, i) =>
    if isIdentifierUse line short then some (i + 1) else none
  unless leftovers.isEmpty do
    IO.eprintln s!"{path}: `{short}` still occurs on line(s) {leftovers} — the info trees did not"
    IO.eprintln "  resolve those; check them by hand before deleting the declaration"

/-- Rewrite every reference in `path` named by `renames`.  The declarations' own binding sites are
    left alone; use `rename-decl` to move both. -/
private def renameReferences (path moduleName : String) (renames : Array Rename) (apply : Bool) :
    IO UInt32 := do
  match ← scanFile path moduleName with
  | .error code => return code
  | .ok scan =>
    let edits ← match batchRenameEdits scan renames (withDefinition := false) with
      | .ok edits => pure edits
      | .error message => IO.eprintln s!"{path}: {message}"; return 1
    if edits.isEmpty then IO.println s!"{path}: no reference to {renameList renames}"; return 0
    reportEdits path scan.source edits
    unless apply do IO.println "preview only; pass --apply to write"; return 0
    let updated := applyEdits scan.source (independentEdits edits).1
    IO.FS.writeFile path updated
    unless ← elaboratesCleanly scan.env path updated do
      IO.FS.writeFile path scan.source
      IO.eprintln s!"{path}: renaming {renameList renames} does not elaborate; restored"
      return 1
    IO.println s!"applied {edits.size} rename(s) to {path}"
    for r in renames do warnLeftovers path updated r.declName
    return 0

/-- Everything `lake` writes for the module compiled from `path`.  A build under a rolled-back edit
    leaves artefacts that match no source, and the `module` system makes that fatal rather than
    merely stale: a file built as a `module` produces `X.olean` PLUS `X.olean.server` and
    `X.olean.private`, and nothing deletes the parts when the source goes back to a plain module and
    `X.olean` is rewritten in the one-file format.  Lean's loader then reads the parts as if they
    described the new `X.olean`, walks the header as though it were objects, and the import NEVER
    RETURNS — measured on this repository as a batch that ran for hours before it was killed.

    So a restore deletes the WHOLE set, never a subset: an `.olean` in `module` format whose parts
    are gone fails to load just as surely, with `missing data file for module X`. -/
private def buildArtefacts (path : String) : Array String :=
  match moduleNameOfPath path with
  | .error _ => #[]
  | .ok moduleName =>
    let base := ".lake/build/lib/lean/" ++ moduleName.replace "." "/"
    #[".olean", ".olean.hash", ".olean.server", ".olean.private", ".ilean", ".trace"].map (base ++ ·)

/-- Delete the artefacts of every path the failed build actually compiled AS A MODULE, and only
    those: the split parts are the evidence, and a module the build never reached still has the
    one-file `.olean` its restored source produced.  The distinction is worth making because the
    `.ilean` goes with the rest, and the index cannot place a declaration without it — deleting the
    whole batch's artefacts costs a whole-repository rebuild before the next attempt can run. -/
private def dropBuildArtefacts (paths : Array String) : IO Unit := do
  for path in paths do
    let artefacts := buildArtefacts path
    let split ← artefacts.filterM fun artefact => do
      pure ((artefact.endsWith ".olean.server" || artefact.endsWith ".olean.private") &&
        (← System.FilePath.pathExists (System.FilePath.mk artefact)))
    if split.isEmpty then continue
    for artefact in artefacts do
      if ← System.FilePath.pathExists artefact then IO.FS.removeFile artefact

/-- Refuse to work in a build tree that already holds the debris above: an `X.olean.server` whose
    source is not a `module`.  Importing such a module never returns, so every operation that
    elaborates would hang with no diagnostic — the check costs one directory walk and names the
    files to delete.  A rolled-back batch cleans up after itself, but a run killed mid-build does
    not, so the guard has to stand in front of the operations rather than only behind them. -/
private def staleSplitParts : IO Bool := do
  let buildDir : System.FilePath := ".lake/build/lib/lean"
  unless ← buildDir.isDir do return false
  let prefixLength := buildDir.toString.length + 1
  let mut stale := #[]
  for part in ← filesEndingIn buildDir ".olean.server" do
    let source := (part.dropEnd ".olean.server".length |>.drop prefixLength).toString ++ ".lean"
    let built ← if ← System.FilePath.pathExists source then
        pure (sourceIsModule (← IO.FS.readFile source)) else pure false
    unless built do stale := stale.push source
  unless stale.isEmpty do
    IO.eprintln <| s!"{stale.size} module(s) have `.olean.server`/`.olean.private` parts but a source \
      that is not a `module`:\n" ++
      String.intercalate "\n" (stale.toList.map ("  " ++ ·)) ++
      "\nImporting one never returns — Lean reads the stale parts as if they described the current \
      `.olean`.\nDelete each module's WHOLE artefact set (`.olean`, `.olean.hash`, `.olean.server`, \
      `.olean.private`, `.ilean`, `.trace`) and rebuild; deleting only the parts leaves \
      `missing data file for module X`."
  return !stale.isEmpty

/-- Run one `lean-refactor` subcommand per matching file, each in a CHILD process.

    Elaborating a file retains its whole `Environment`, so looping over a glob IN-PROCESS
    accumulates one environment per file.  Measured: a `rename --glob 'Freyd/*.lean'` over 200+
    modules reached 18.3 GB resident and was OOM-killed.  A child per file hands the memory back at
    every step, and one file's failure no longer takes the run down.

    The child is THIS binary (`IO.appPath`), not `lake exe lean-refactor`: lake re-resolves the
    package on every invocation, which measured 110 ms of the 305 ms a small file costs, and the
    parent is by construction the up-to-date build that a `lake exe` would have selected. -/
private def forkPerFile (pattern : String) (childArgs : String → Array String)
    (mentioning : Array String := #[]) : IO UInt32 := do
  if ← staleSplitParts then return 1
  let selected ← globSelectedFiles pattern mentioning
  if selected.isEmpty then return 1
  let self := (← IO.appPath).toString
  let outputs ← mapFilesParallel (← scanJobs) selected fun path =>
    IO.Process.output { cmd := self, args := childArgs path }
  let mut status : UInt32 := 0
  for output in outputs do
    unless output.stdout.isEmpty do IO.print output.stdout
    unless output.stderr.isEmpty do IO.eprint output.stderr
    if output.exitCode != 0 then status := output.exitCode
  return status

/-- The freshness guard.  A source file EDITED BUT NOT REBUILT has an unchanged `.ilean` whose
    recorded positions have moved, so the index would point at stale text.  A file may use the
    fast path only when its `.ilean` is at least as new as the source; a missing file of either
    side also fails the guard.  `metadata` throws for a missing file, and the throw is the guard. -/
private def ileanAtLeastAsNew (path : String) : IO Bool := do
  let some moduleName := moduleNameOfPath path |>.toOption
    | return false
  let ileanPath := System.FilePath.mk ".lake/build/lib/lean" /
    System.FilePath.mk (moduleName.replace "." "/" ++ ".ilean")
  try
    let sourceModified := (← (System.FilePath.mk path).metadata).modified
    let ileanModified := (← ileanPath.metadata).modified
    return match compare ileanModified sourceModified with
      | .lt => false  -- source is newer than its `.ilean`: the positions may have moved
      | _ => true
  catch _ => return false

/-- The whole fast-path file output, in the same shape a forked child would have produced: the
    `reportEdits` lines and the preview note on stdout, a batch refusal on stderr, the same exit
    codes as `renameReferences`.  No file is elaborated; the sites come from the index. -/
private def fastRenameFileOutput (path : String) (renames : Array Rename)
    (sitesByDecl : Std.HashMap String (Array Query.Site)) : IO IO.Process.Output := do
  let source ← IO.FS.readFile path
  let fileMap := (Parser.mkInputContext source path).fileMap
  match indexBatchRenameEdits fileMap source renames sitesByDecl with
  | .error message => return { stdout := "", stderr := s!"{path}: {message}", exitCode := 1 }
  | .ok edits =>
      if edits.isEmpty then
        return { stdout := s!"{path}: no reference to {renameList renames}\n", stderr := "",
                 exitCode := 0 }
      let lines := (reportLines path source edits).map (· ++ "\n")
      let lines := lines.push "preview only; pass --apply to write\n"
      return { stdout := String.intercalate "" lines.toList, stderr := "", exitCode := 0 }

/-- Refresh the target repository's index and return its database path.  Any failure — no build
    directory, the refresh throws — prints the one-line unavailability note on stderr and returns
    `none`; the callers then fall back to per-file elaboration, never aborting a rename because
    the index is unavailable. -/
private def refreshedIndex? : IO (Option String) := do
  let buildDir := ".lake/build/lib/lean"
  unless ← System.FilePath.isDir buildDir do
    IO.eprintln s!"refactor index unavailable: {buildDir} does not exist; \
      falling back to per-file elaboration"
    return none
  -- BEFORE the refresh, which imports every stale module: an orphaned split part makes that import
  -- spin in `compacted_region::read` and never return.  `stagedGlob` runs the same guard for its
  -- verify build, but a driver consults the index FIRST, so the guard there is reached only after
  -- the hang it was written to prevent — measured at 37 minutes of a `modularize --glob` that had
  -- printed nothing.
  if ← staleSplitParts then return none
  let dbPath := ".lake/build/refactor-index.db"
  try
    _ ← Index.refresh dbPath buildDir false
    pure (some dbPath)
  catch e =>
    IO.eprintln s!"refactor index unavailable ({toString e}); falling back to per-file elaboration"
    pure none

/-- The index half of the glob driver: a silent refresh at the target repository's
    `.lake/build/refactor-index.db`, then every rename's use sites grouped by source path, with the
    database path for the callers that need it.  Any failure — no build directory, refresh throws —
    yields `none` and prints one line on stderr; the caller then falls back to the per-file
    elaboration path, never aborting a rename because the index is unavailable. -/
private def indexSitesByPath (renames : Array Rename) :
    IO (Option (String × Std.HashMap String (Std.HashMap String (Array Query.Site)))) := do
  try
    let some dbPath ← refreshedIndex? | return none
    let mut byPath : Std.HashMap String (Std.HashMap String (Array Query.Site)) := {}
    for r in renames do
      let sites ← Query.useSitesByFile dbPath r.declName
      for (path, fileSites) in sites do
        let perDecl := byPath.getD path {}
        byPath := byPath.insert path (perDecl.insert r.declName fileSites)
    pure (some (dbPath, byPath))
  catch e =>
    IO.eprintln s!"refactor index unavailable ({toString e}); falling back to per-file elaboration"
    pure none

/-- One warning line after a rename preview: modules that depend on `declName` without naming it
    anywhere the info trees recorded — reached only through notation or macro expansion.  No edit is
    needed there, the notation is declared once, but they must still compile: they are exactly the
    modules a rename can break without touching.  The list is `lean-refactor uses`'s job; this is
    one line. -/
private def warnSilentDependents (dbPath declName : String) : IO Unit := do
  let dependents ← Query.silentDependents dbPath declName
  unless dependents.isEmpty do
    IO.eprintln (s!"{dependents.size} module(s) depend on {declName} without naming it (notation or " ++
      s!"macro expansion); no edit is needed there, but\n" ++
      s!"  they must still compile — `lean-refactor uses {declName}` lists them")

/-- `lean-refactor uses`: what the two halves of the index each see for `declName`, as source paths
    — the modules with recorded use sites, the modules that depend without naming it, and the
    modules that name it without depending on it.  A read-only report; the caller edits files, so
    every module name is joined to its `module.source` path first. -/
private def usesReport (declName : String) : IO UInt32 := do
  let some dbPath ← refreshedIndex? | return 1
  let sites ← Query.useModules dbPath declName
  let dependents ← Query.dependentModules dbPath declName
  let silent ← Query.silentDependents dbPath declName
  let sources ← Query.moduleSources dbPath
  let pathOf (module : String) : String := sources.getD module module
  let used := (sites.map fun (module, count) => (pathOf module, count)).qsort (·.1 < ·.1)
  let namedWithout := sites.filter fun (module, _) => !dependents.contains module
  let namedPaths := (namedWithout.map (fun (module, _) => pathOf module)).qsort (· < ·)
  let silentPaths := (silent.map pathOf).qsort (· < ·)
  IO.println s!"{declName}: {sites.foldl (fun total (_, count) => total + count) 0} site(s) in {sites.size} module(s), {dependents.size} module(s) depend on it"
  unless used.isEmpty do
    IO.println "  used in:"
    for (path, count) in used do IO.println s!"    {path}: {count}"
  unless silentPaths.isEmpty do
    IO.println s!"  depend without naming it ({silentPaths.size}):"
    for path in silentPaths do IO.println s!"    {path}"
  unless namedPaths.isEmpty do
    IO.println s!"  name it without depending on it ({namedPaths.size}):"
    for path in namedPaths do IO.println s!"    {path}"
  return 0

/-! ## Adopting the module system

`module` is opt-in per file, and adopting it takes three edits at once: the `module` keyword, every
`import` turned into a `public import`, and `public` on each declaration something outside the file
names.  The index answers the third — every `dep` edge whose using module is not the declaring one —
and the first two are line-oriented.

Every import becomes public, which is exactly what an import means today: without the module system
it is transitively visible to everything downstream, so making them all public preserves the
current meaning. Narrowing them is a separate pass, and once a repository is on the module system
`lake shake` is the tool for it.

The edits cannot disturb each other, because none of them is a line number. Each is a byte range
into the source as read; `independentEdits` refuses any pair that overlaps; and `applyEdits` sorts
DESCENDING on `start` and folds, so every edit still to be applied points exactly where it did when
it was computed.

Nothing here is imported.  Where each declaration begins — and where its attribute bracket and its
modifiers end — the index answers from the `syntax_node` table, which the same build that produced
the `.olean` also produced, so the whole operation is a scan of the source plus one query.  The
only text scan left is the imports, which are line-oriented, and a file whose source is newer than
its `.ilean` is elaborated instead of trusting a stale tree. -/

/-- The edits that put one file on the module system, as byte ranges into `source`, with the report
    line.  With `checkImports`, refuse an import that is not yet a module — right for one file,
    wrong for a batch, where the whole set becomes a module together and only the final build can
    judge.  `sites` are the 0-based LSP positions of the declarations the index says something
    outside the file names; `decls` are the same file's declarations as its command tree reads
    them, and every site is resolved against them by name. -/
private def modularizeEdits (path source : String) (nodes : Array SyntaxRows.Node)
    (sites : Array (String × Nat × Nat × Bool)) (decls : Array SyntaxQuery.Decl)
    (checkImports : Bool) : IO (Except String (Array Edit × String)) := do
  let lines := source.splitOn "\n"
  if sourceIsModule source then
    return .error s!"{path}: already on the module system"
  let mut edits : Array Edit := #[]
  let mut offset : String.Pos.Raw := ⟨0⟩
  let mut imports := 0
  for line in lines do
    -- Line-oriented and exact, as `rename-module`'s import edits are: only a module name follows the
    -- keyword, so no docstring or declaration can match.
    if line.trimAsciiStart.toString.startsWith "import " then
      -- A module name has no space, so the token is the whole name even when a trailing comment
      -- follows it — `import AOP.A4_2  -- entire_id_le` names `AOP.A4_2`, and the old read kept
      -- the comment, building a path that did not exist and letting the gate pass silently.
      let imported := String.takeWhile
        ((line.trimAscii.toString.drop "import ".length).trimAsciiStart.toString) (fun c => c != ' ')
      -- `cannot import non-`module` X from `module`` — the conversion is not per-file: a file can
      -- only become a module once everything it imports already is one, so the repository has to be
      -- walked bottom-up through the import graph.  An import whose source is not in this repository
      -- is Lean's own, which is already on the module system.  A batch skips the check: the whole
      -- set becomes a module together, so it would only refuse files that the set itself fixes.
      if checkImports then
        let importedPath := System.FilePath.mk (imported.replace "." "/" ++ ".lean")
        if ← System.FilePath.pathExists importedPath then
          unless sourceIsModule (← IO.FS.readFile importedPath) do
            return .error s!"{path}: `{imported}` ({importedPath}) is not a `module` yet, and a module \
              cannot import one that is not; convert it first"
      -- The keyword and the first import's `public` are ONE edit, not two. Two zero-width edits at
      -- the same offset do not overlap, so `independentEdits` accepts both, and `applyEdits` sorts
      -- on `start` alone — leaving their order to the sort, which wrote `public module` half the
      -- time and broke every file that had it.
      let header := if imports == 0 then "module\n\npublic " else "public "
      edits := edits.push { start := offset, stop := offset, line := 0, replacement := header }
      imports := imports + 1
    offset := ⟨offset.byteIdx + line.utf8ByteSize + 1⟩
  -- A root module imports nothing, so there is no import line to hang the keyword on; it goes at the
  -- very start, above the banner comment, which is the only position that needs no parsing.
  if imports == 0 then
    edits := edits.push { start := ⟨0⟩, stop := ⟨0⟩, line := 0, replacement := "module\n\n" }
  let fileMap := FileMap.ofString source
  -- Sites are resolved to declarations FIRST, and a declaration reached twice is marked once.  The
  -- index reports a site per NAME, and several names land on one declaration: every field, ctor and
  -- recursor of a structure is its own row and `memberOf` sends them all to the structure.  Writing
  -- one edit per site made `AOP/A5_1` report 11 marks for the 6 declarations it has, and — worse —
  -- two sites disagreeing about exposure would emit two DIFFERENT edits at one offset, which
  -- `independentEdits` refuses, failing the file for a disagreement that concerns two different
  -- declarations.  Exposure is a union: a member's taint says nothing about its parent's body, so it
  -- must not veto, and an exposure that turns out wrong fails the build loudly.
  let mut resolved : Std.HashMap Nat (SyntaxQuery.Decl × Bool) := {}
  for (declName, line, column, exposable) in sites do
    -- The tree is what the source actually writes, and the index's name is checked against it: a
    -- name the tree does not know means the index describes a source edited since its build, and
    -- `public ` written at a position that has moved lands in front of the WRONG declaration —
    -- valid syntax, so no build would catch it.  The index's (line, column) is only the tiebreak
    -- for a name written twice in one file.
    -- `matchDecl` is name-primary; `memberOf` extends it to the fields, constructors, and
    -- recursors the index names — sites whose parent declaration is the thing that must be
    -- marked, since a public structure or inductive publishes its members.
    let decl := match SyntaxQuery.matchDecl decls declName line column fileMap with
      | some decl => some decl
      | none => SyntaxQuery.memberOf decls declName
    match decl with
    | none =>
        -- Neither a declaration of this file nor a member of one: either the index describes a
        -- source that has since been edited, or the name the file no longer contains.  The old
        -- pass tolerated the second when the word at the recorded position still belonged to the
        -- name — a field of a structure the index has not caught up with — and a position that
        -- says nothing about the name is exactly the stale index worth a rebuild.
        let byte := (fileMap.lspPosToUtf8Pos ⟨line, column⟩).byteIdx
        if (declName.splitOn ".").contains (SyntaxQuery.wordAt nodes source byte) then pure ()
        else return .error s!"{path}:{line + 1}: the index puts `{declName}` where the source has \
          no matching declaration; rebuild before marking it"
    | some decl =>
        -- The source fixes the visibility itself, and what it wrote wins.
        unless decl.visibility != "" do
          -- `public` says the NAME is visible downstream, `@[expose]` that the BODY is, and the two
          -- travel together here: the public set is closed under what a public body mentions, so
          -- exposing exactly it leaves no exposed body naming an unexposed constant.  A `theorem`
          -- is never exposed — proof irrelevance means no downstream elaboration needs its value —
          -- and Lean refuses the attribute on anything but a `def`, which `abbrev` and `instance`
          -- are.  A body that names a `private` constant cannot be published at all, so it stays
          -- unexposed.
          let exposed := exposable && #["def", "abbrev", "instance"].contains decl.keyword
          resolved := resolved.insert decl.kw
            (decl, exposed || (resolved.get? decl.kw |>.any (·.2)))
  for (_, decl, exposed) in resolved.toArray do
    -- Two attribute brackets in a row do not parse, so an existing one is joined rather than
    -- preceded.  `@[simp, expose] public theorem` is the shape Lean accepts.
    match (if exposed then decl.attributes.map (·.2 - 1) else none) with
    | some bracket =>
        edits := edits.push
          { start := ⟨bracket⟩, stop := ⟨bracket⟩, line := 0, replacement := ", expose" }
        edits := edits.push
          { start := ⟨decl.slot⟩, stop := ⟨decl.slot⟩, line := 0, replacement := "public " }
    | none =>
        -- ONE edit, not two at one offset: two zero-width edits there have no order, which is the
        -- mistake that once wrote `public module`.
        let header := if exposed then "@[expose] public " else "public "
        edits := edits.push
          { start := ⟨decl.slot⟩, stop := ⟨decl.slot⟩, line := 0, replacement := header }
  return .ok (edits,
    s!"{path}: `module`, {imports} public import(s), {resolved.size} public declaration(s)")

/-- `lean-refactor modularize`: put one file on the module system, verifying that it still
    elaborates. Visibility is the only thing here the index decides, and it decides it from the
    dependency edges — a declaration is public exactly when something outside this file names it. -/
private def modularize (path : String) (apply : Bool) : IO UInt32 := do
  let some dbPath ← refreshedIndex? | return 1
  let source ← IO.FS.readFile path
  let moduleName ← IO.ofExcept (moduleNameOfPath path)
  -- The tree the index holds is as new as the `.olean` it was built with, and the staleness guard
  -- the rename fast path uses is the same here: a source edited since the last build is elaborated
  -- in this process instead of being marked at positions that have moved.
  let nodes ← if ← ileanAtLeastAsNew path then SyntaxQuery.nodesOfModule dbPath moduleName
    else SyntaxQuery.nodesOfFile path moduleName
  let decls := SyntaxQuery.declarationsOf nodes source
  let sites ← Query.publicDeclSites dbPath moduleName (SyntaxQuery.instanceLinesOf decls source)
  let (edits, summary) ← match ← modularizeEdits path source nodes sites decls true with
    | .error message => IO.eprintln message; return 1
    | .ok result => pure result
  IO.println summary
  let (selected, deferred) := independentEdits edits
  if deferred != 0 then
    IO.eprintln s!"{path}: refusing {deferred} overlapping edit(s)"
    return 1
  unless apply do IO.println "preview only; pass --apply to write"; return 0
  let updated := applyEdits source selected
  IO.FS.writeFile path updated
  initSearchPath (← findSysroot)
  unless ← fileElaboratesCleanly path updated do
    IO.FS.writeFile path source
    IO.eprintln s!"{path}: the modularised source does not elaborate; restored"
    return 1
  IO.println s!"applied {selected.size} edit(s) to {path}"
  return 0

/-- Stage one file for the batch driver: the edits go to `stagePath`, never to `path`, and the
    report comes back in the shape `stagedGlob` collects.  Exit 3 means the file is already a
    module, which is not a failure for a batch.  There is no per-file verify: mid-batch a converted
    file's imports are not yet rebuilt, so the one repository build at the end is the gate.
    Staging itself elaborates nothing — the tree the edits read came from the index or a
    `syntax-rows` child — so there is no `Environment` to hand back. -/
private def modularizeStage (path stagePath : String) (nodes : Array SyntaxRows.Node)
    (sites : Array (String × Nat × Nat × Bool)) (decls : Array SyntaxQuery.Decl) :
    IO IO.Process.Output := do
  let source ← IO.FS.readFile path
  match ← modularizeEdits path source nodes sites decls false with
  | .error message =>
      if message.endsWith "already on the module system" then
        return { stdout := message ++ "\n", stderr := "", exitCode := 3 }
      return { stdout := "", stderr := message ++ "\n", exitCode := 1 }
  | .ok (edits, summary) =>
      let (selected, deferred) := independentEdits edits
      if deferred != 0 then
        return { stdout := "", stderr := s!"{path}: refusing {deferred} overlapping edit(s)\n",
                 exitCode := 1 }
      IO.FS.writeFile stagePath (applyEdits source selected)
      return { stdout := summary ++ "\n", stderr := "", exitCode := 0 }

/-- `lean-refactor dup`: pieces of source the repository writes more than once.

    The key is the SYNTAX TREE, which is the one thing an elaborated term cannot report.  A `by`
    block reaches the `.olean` as the term its tactics produced, so two copies of one tactic script
    run against slightly different goals leave different terms behind and no term-keyed pass groups
    them — while the source is a copy-paste.  Identifiers are blanked in the key, so the same proof
    written for `≤` and for `≥` is one group; every other token is kept, so `3` is not `5`.

    Subtrees, not declarations: the report is about the repeated FRAGMENT, which is what a reader
    can factor out, and a repeated whole declaration is just the case where the fragment is the
    whole thing.

    A group is a candidate, not a task.  Nothing here checks that the occurrences can see one
    another, and a shape that repeats because Lean's syntax gives it no other spelling is not a
    duplicate — which is what `--min-nodes` is for. -/
private def dupReport (minNodes : Nat) : IO UInt32 := do
  let some dbPath ← refreshedIndex? | return 1
  let groups ← Query.cloneGroups dbPath minNodes
  IO.println s!"{groups.size} repeated fragment(s) of ≥ {minNodes} node(s)"
  -- One read per file however many occurrences it holds: a big clone group crosses few files and a
  -- long report revisits them.
  let mut sources : Std.HashMap String (String × FileMap) := {}
  for group in groups do
    let files := group.sites.foldl (fun (s : Std.HashSet String) site => s.insert site.source) ∅
    IO.println s!"  {group.sites.size}× in {files.size} file(s), {group.nodes} nodes:"
    for site in group.sites do
      unless sources.contains site.source do
        let text ← try IO.FS.readFile site.source catch _ => pure ""
        sources := sources.insert site.source (text, FileMap.ofString text)
      let (text, fileMap) := sources[site.source]!
      let line := (fileMap.toPosition ⟨site.b0⟩).line
      -- The first line of the occurrence, so a group can be judged without opening anything.
      let head := (String.Pos.Raw.extract text ⟨site.b0⟩ ⟨min site.b1 text.rawEndPos.byteIdx⟩)
        |>.splitOn "\n" |>.headD ""
      IO.println s!"    {site.source}:{line}  {head.trimAscii}"
  return 0

/-- The glob driver.  In preview the index answers where the references are without elaborating
    the files — a repository-wide rename spends its minutes recomputing what `lake build` already
    wrote to `.ilean`, and the index holds exactly those positions.  A file takes the fast path
    when the freshness guard passes, whether or not the index has sites there: a fresh index that
    records nothing for the file is itself the "no reference" answer.  A file whose `.ilean` is
    missing or older than its source is elaborated by a child as before — the index may be silent
    where the elaborated file would speak.  `--apply` cannot use the fast path: applying
    re-elaborates each file to verify the result, which is the elaboration the fast path skips. -/
private def renameGlob (pattern : String) (renames : Array Rename) (apply noIndex : Bool) :
    IO UInt32 := do
  let mentioning := renames.map fun r => shortName r.declName
  let fast? ← if apply || noIndex then pure none else indexSitesByPath renames
  let selected ← globSelectedFiles pattern mentioning
  if selected.isEmpty then return 1
  let self := (← IO.appPath).toString
  let childArgs := fun path => #["rename-file", path] ++ renameArgs renames ++
    (if apply then #["--apply"] else #[])
  let outputs ← mapFilesParallel (← scanJobs) selected fun path => do
    match fast? with
    | some (_, byPath) =>
        if ← ileanAtLeastAsNew path then
          fastRenameFileOutput path renames (byPath.getD path {})
        else
          IO.Process.output { cmd := self, args := childArgs path }
    | none => IO.Process.output { cmd := self, args := childArgs path }
  let mut status : UInt32 := 0
  for output in outputs do
    unless output.stdout.isEmpty do IO.print output.stdout
    unless output.stderr.isEmpty do IO.eprint output.stderr
    if output.exitCode != 0 then status := output.exitCode
  if let some (dbPath, _) := fast? then
    for r in renames do warnSilentDependents dbPath r.declName
  return status

/-! ## Renaming a declaration

`rename` moves the USES of a declaration and checks each file on its own.  That check is exactly
what a real rename cannot pass: the moment the binding site moves, every file still on the old name
stops elaborating, and every file already on the new name stops elaborating until the binding site
moves.  No ordering of per-file edits makes both halves valid at once.

So `rename-decl` splits the work.  Each file is analysed in a CHILD process (one `Environment` per
process — see `forkPerFile`) that writes its result to a STAGING file and leaves the original
alone.  Only when every file has staged successfully are the originals replaced, and the check is
then a single capped whole-repository build.  A failure restores every file, so the operation is
transactional at repository scale — the same contract as `rename-module`. -/

private def stagePathFor (path : String) : String := path ++ ".rename-stage"

private def dropStagedFiles (staged : Array String) : IO Unit := do
  for path in staged do
    let stage := stagePathFor path
    if ← System.FilePath.pathExists stage then IO.FS.removeFile stage

/-- Analyse one file for a whole BATCH of renames and write the renamed text to `stagePath`, never to
    `path`.  Exit 3 means the file names none of the declarations, which is not an error. -/
private def renameDeclStage (path stagePath : String) (renames : Array Rename) : IO UInt32 := do
  let moduleName ← match moduleNameOfPath path with
    | .ok name => pure name
    | .error message => IO.eprintln message; return 2
  match ← scanFile path moduleName with
  | .error code => return code
  | .ok scan =>
    let edits ← match batchRenameEdits scan renames (withDefinition := true) with
      | .ok edits => pure edits
      | .error message => IO.eprintln s!"{path}: {message}"; return 1
    if edits.isEmpty then IO.println s!"{path}: no reference to {renameList renames}"; return 3
    reportEdits path scan.source edits
    let updated := applyEdits scan.source (independentEdits edits).1
    IO.FS.writeFile stagePath updated
    for r in renames do warnLeftovers path updated r.declName
    return 0

/-- Fork a staging child per file, swap every staged file in at once, and check with ONE capped
    repository build; any failure restores every file.  This is the shape a cross-file edit needs —
    no per-file check can pass while the change is half applied.  A child exits 3 to say its file is
    not affected, which is not a failure. -/
private def stagedGlob (pattern description : String)
    (stage : String → String → IO IO.Process.Output)
    (apply : Bool) (mentioning : Array String := #[]) : IO UInt32 := do
  if ← staleSplitParts then return 1
  let selected ← globSelectedFiles pattern mentioning
  if selected.isEmpty then return 1
  let outputs ← mapFilesParallel (← scanJobs) selected fun path => stage path (stagePathFor path)
  let mut staged : Array String := #[]
  let mut failed := false
  for (path, output) in selected.zip outputs do
    unless output.stdout.isEmpty do IO.print output.stdout
    unless output.stderr.isEmpty do IO.eprint output.stderr
    if output.exitCode == 0 then staged := staged.push path
    else if output.exitCode != 3 then failed := true
  let stagedFiles := staged
  if failed then
    dropStagedFiles stagedFiles
    IO.eprintln s!"staging failed ({description}); nothing was written"
    return 1
  if stagedFiles.isEmpty then
    IO.eprintln s!"no file matching `{pattern}` is affected: {description}"
    return 1
  unless apply do
    dropStagedFiles stagedFiles
    IO.println "preview only; pass --apply to write"
    return 0
  let mut backups : Array (String × String) := #[]
  for path in stagedFiles do
    backups := backups.push (path, ← IO.FS.readFile path)
    IO.FS.writeFile path (← IO.FS.readFile (stagePathFor path))
  dropStagedFiles stagedFiles
  let restore := backups
  let build ← repositoryBuild
  unless build.stdout.isEmpty do IO.eprint build.stdout
  unless build.stderr.isEmpty do IO.eprint build.stderr
  if build.exitCode != 0 then
    for (path, source) in restore do IO.FS.writeFile path source
    dropBuildArtefacts stagedFiles
    -- Restoring the sources is not restoring the repository: the artefacts just dropped are what
    -- the index reads, and a module missing from the index is one this pass reports as never built
    -- and leaves alone.  Skipping the rebuild once cost a whole attempt, whose only failures were
    -- three modules importing two the batch had silently passed over.
    let recover ← repositoryBuild
    if recover.exitCode != 0 then
      IO.eprint recover.stdout
      IO.eprint recover.stderr
      IO.eprintln s!"whole-repository build failed ({description}); sources restored, but the \
        rebuild that puts the index back FAILED — run the repository build before trying again"
      return recover.exitCode
    IO.eprintln s!"whole-repository build failed ({description}); restored"
    return build.exitCode
  IO.println s!"{description}: {stagedFiles.size} file(s); build passed"
  return 0

private def renameDeclGlob (pattern : String) (renames : Array Rename) (apply : Bool) : IO UInt32 := do
  let dbPath? ← refreshedIndex?
  let self := (← IO.appPath).toString
  let status ← stagedGlob pattern s!"renamed {renameList renames}"
    (fun path stage => IO.Process.output
      { cmd := self, args := #["rename-decl-stage", path, stage] ++ renameArgs renames }) apply
    (mentioning := renames.map fun r => shortName r.declName)
  if let some dbPath := dbPath? then
    for r in renames do warnSilentDependents dbPath r.declName
  return status

/-- The command tree of a file the index cannot answer for, from a `syntax-rows` child — the same
    one-file-per-process shape every elaboration takes here, since an `Environment` per file is
    what reached 18.3 GB once.  The child's stdout is exactly the record stream the index driver
    imports. -/
private def nodesOfChild (path : String) : IO (Array SyntaxRows.Node) := do
  let self := (← IO.appPath).toString
  let child ← IO.Process.output { cmd := self, args := #["syntax-rows", path] }
  if child.exitCode != 0 then
    throw <| IO.userError s!"{path}: the `syntax-rows` child failed: {child.stderr}"
  pure (SyntaxQuery.nodesOfRows ((child.stdout.splitOn Db.recordSep).toArray))

/-- `lean-refactor modularize --glob`: put every file matching the pattern on the module system
    together, staging per file and swapping all in at once — the shape `rename-decl` uses for
    exactly this situation.  The batch keeps no `Environment`: the index answers where each
    declaration is, and a file whose tree the index holds is trusted only as far as its `.olean`
    reaches — a source edited since is elaborated by a `syntax-rows` child, one file per process. -/
private def modularizeGlob (pattern : String) (apply : Bool) : IO UInt32 := do
  let some dbPath ← refreshedIndex? | return 1
  let indexed ← Query.moduleSources dbPath
  let mut sites : Std.HashMap String (Array (String × Nat × Nat × Bool)) := {}
  let mut declsOf : Std.HashMap String (Array SyntaxQuery.Decl) := {}
  let mut nodesOf : Std.HashMap String (Array SyntaxRows.Node) := {}
  let mut unbuilt := #[]
  let mut blockers : Array (String × String × String × Bool) := #[]
  for path in ← globSelectedFiles pattern do
    let moduleName ← IO.ofExcept (moduleNameOfPath path)
    -- A module the index has never seen was never built, so nothing is known about what names it
    -- from outside and converting it would mark nothing `public`.  It is left alone instead: a
    -- module may not import a plain module, but a plain module may import a module, so a file
    -- outside the build blocks nothing — and nothing imports it either, or it would be built.
    if indexed.contains moduleName then
      let source ← IO.FS.readFile path
      let nodes ← if ← ileanAtLeastAsNew path then SyntaxQuery.nodesOfModule dbPath moduleName
        else nodesOfChild path
      let decls := SyntaxQuery.declarationsOf nodes source
      declsOf := declsOf.insert path decls
      nodesOf := nodesOf.insert path nodes
      let lines := SyntaxQuery.instanceLinesOf decls source
      sites := sites.insert path (← Query.publicDeclSites dbPath moduleName lines)
      for (instanceName, blocked, needed) in ← Query.privateBlockers dbPath moduleName lines do
        blockers := blockers.push (path, instanceName, blocked, needed)
    else
      unbuilt := unbuilt.push path
  unless unbuilt.isEmpty do
    IO.println <| s!"leaving {unbuilt.size} file(s) alone: never built, so the index knows nothing \
      about what names them:\n" ++ String.intercalate "\n" (unbuilt.toList.map ("  " ++ ·))
  -- Reported rather than attempted: no marking this pass can write makes a public instance's body
  -- able to name a private constant, so the source has to drop the `private` first.
  unless blockers.isEmpty do
    let line (path instanceName blocked : String) (needed : Bool) : String :=
      s!"  {path}: `private {blocked}` is named by the body of `instance {instanceName}`" ++
        (if needed then ", which something outside the file depends on" else "")
    IO.eprintln <| s!"{blockers.size} `private` declaration(s) block the conversion — an instance is \
      public whether or not anything outside names it, and a public instance publishes its body:\n" ++
      String.intercalate "\n"
        (blockers.toList.map fun (path, instanceName, blocked, needed) =>
          line path instanceName blocked needed)
    return 1
  -- Exit 3 is `stagedGlob`'s "this file is not affected", which is exactly an unbuilt one's case.
  stagedGlob pattern "put on the module system" (fun path stage =>
    match sites[path]?, declsOf[path]?, nodesOf[path]? with
    | some fileSites, some decls, some nodes => modularizeStage path stage nodes fileSites decls
    | _, _, _ => pure { stdout := "", stderr := "", exitCode := 3 }) apply

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
  forkPerFile pattern
    (fun path => #["rename-token", path, oldToken, newToken] ++ (if apply then #["--apply"] else #[]))
    (mentioning := #[oldToken])

/-! ## Applied form to infix

A binary declaration that has notation — `OrderedCat.le` and its `≤` — should be READ through the
notation, or the source says one thing and the paper it transcribes says another.  Rewriting
`f a b` to `a ⊗ b` by hand is where paren errors come from, so the argument spans are taken from
the parse tree: whatever text the source gave each argument, including its parentheses, is what is
emitted around the token.  The edit is source-level only — `f a b` and `a ⊗ b` are the same term. -/

private def identNames (declName : String) (id : String) : Bool :=
  declName == id || declName.endsWith ("." ++ id)

/-- The span to read an operand from.  A function application or a bare name never needs brackets
    around it, at any operator precedence, so the author's parentheses come off — that is what turns
    `OrderedCat.le (𝟙 a) R` into `𝟙 a ≤ R` rather than `(𝟙 a) ≤ R`.  Anything else keeps exactly the
    text the author wrote: whether THAT needs bracketing is a precedence question, and guessing it
    wrong changes the term. -/
private partial def unwrapOperand (stx : Syntax) : Syntax :=
  if stx.isOfKind ``Lean.Parser.Term.paren || stx.isOfKind nullKind then
    match stx.getArgs.filter fun child => !child.isAtom && child.getRange?.isSome with
    | #[inner] => unwrapOperand inner
    | _ => stx
  else stx

private def operandRange (stx : Syntax) : Option Lean.Syntax.Range :=
  let inner := unwrapOperand stx
  if inner.isOfKind ``Lean.Parser.Term.app || inner.isIdent then inner.getRange? else stx.getRange?

private partial def infixSites (stx : Syntax) (declName token source : String) : Array Edit :=
  Id.run do
  let mut edits := #[]
  for child in stx.getArgs do
    edits := edits ++ infixSites child declName token source
  if stx.isOfKind ``Lean.Parser.Term.app then
    let fn := stx[0]
    let args := stx[1].getArgs
    if fn.isIdent && identNames declName fn.getId.toString && args.size == 2 then
      if let (some whole, some left, some right) :=
          (stx.getRange?, operandRange args[0]!, operandRange args[1]!) then
        let text (r : Lean.Syntax.Range) := String.Pos.Raw.extract source r.start r.stop
        let written := s!"{text left} {token} {text right}"
        edits := edits.push
          { start := whole.start, stop := whole.stop, line := 0, replacement := written }
  return edits

/-- Stage `path` with every application of `declName` written infix with `token`. -/
private def infixStage (path declName token stagePath : String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let (source, fileMap, commands, _) ← elaborateFile path
  let mut edits := #[]
  for cmd in commands do
    edits := edits ++ infixSites cmd declName token source
  if edits.isEmpty then IO.println s!"{path}: no application of `{declName}`"; return 3
  let positioned := edits.map fun edit =>
    { edit with line := (fileMap.toPosition edit.start).line + 1 }
  let (selected, deferred) := independentEdits positioned
  if deferred > 0 then IO.println s!"{path}: deferred {deferred} nested application(s)"
  for edit in selected do
    IO.println s!"{path}:{edit.line}: {repr (String.Pos.Raw.extract source edit.start edit.stop)} -> {repr edit.replacement}"
  IO.FS.writeFile stagePath (applyEdits source selected)
  return 0

private def infixGlob (pattern declName token : String) (apply : Bool) : IO UInt32 := do
  let self := (← IO.appPath).toString
  stagedGlob pattern s!"wrote `{declName}` infix as `{token}`"
    (fun path stage => IO.Process.output
      { cmd := self, args := #["infix-stage", path, declName, token, stage] }) apply
    (mentioning := #[shortName declName])

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
  "usage:\n  lean-refactor index [--full]\n  lean-refactor uses <full-declaration-name>\n  lean-refactor dup [--min-nodes <n>]\n  lean-refactor modularize <source.lean> [--apply]\n  lean-refactor modularize --glob '<pattern>' [--apply]\n  lean-refactor lint-book-file <source.lean>\n  lean-refactor lint-book --glob '<pattern>'\n  lean-refactor rename-module <old-module> <new-module> [--apply]\n  lean-refactor move <source.lean> <full-declaration-name> <target.lean> [--apply]\n  lean-refactor move-into <source.lean> <full-declaration-name> <target.lean> <target-namespace> [--apply]\n  lean-refactor move-omit <source.lean> <full-declaration-name> <target.lean> <binders> [--apply]\n  lean-refactor relocate-before <source.lean> <full-declaration-name> <anchor-declaration> [--apply]\n  lean-refactor relocate-before-section <source.lean> <full-declaration-name> <section-name> [--apply]\n  lean-refactor collapse <source.lean> <full-declaration-name> <replacement> [--apply]\n  lean-refactor collapse-drop-call-arg <source.lean> <full-declaration-name> <replacement> <1-based-index> [--apply]\n  lean-refactor replace-body <source.lean> <full-declaration-name> <term> [--apply]\n  lean-refactor replace-declaration <source.lean> <full-declaration-name> <declaration> [--apply]\n  lean-refactor remove-declaration <source.lean> <full-declaration-name> [--apply]\n  lean-refactor rename <source.lean> <module> (<full-declaration-name> <replacement>)... [--apply]\n  lean-refactor rename --glob '<pattern>' (<full-declaration-name> <replacement>)... [--apply] [--no-index]\n  lean-refactor rename-decl --glob '<pattern>' (<full-declaration-name> <replacement>)... [--apply]\n  lean-refactor rename-file <source.lean> (<full-declaration-name> <replacement>)... [--apply]\n  lean-refactor rename-token <source.lean> <old-token> <new-token> [--apply]\n  lean-refactor rename-token --glob '<pattern>' <old-token> <new-token> [--apply]\n  lean-refactor infix --glob '<pattern>' <full-declaration-name> <token> [--apply]\n  lean-refactor unused <source.lean>:<line>:<column> [--apply]\n  lean-refactor unused --glob '<pattern>' [--apply]\n  lean-refactor unused-simp --glob '<pattern>' [--apply]\n  lean-refactor inspect <source.lean> <module> <declaration-module> <full-declaration-name>\n  lean-refactor remove-call-arg <source.lean> <module> <declaration-module> <full-declaration-name> <1-based-index> [--syntax] [--token <notation-token>] [--apply]\n  lean-refactor insert-call-arg <source.lean> <module> <declaration-module> <full-declaration-name> <before-1-based-index> <term> [--apply]\n  lean-refactor remove-parameter <source.lean> <module> <full-declaration-name> <binder-name> <1-based-index> [--apply]\n\na glob pattern is a comma-separated list; a leading `!` subtracts:\n  --glob 'Freyd/*.lean,!Freyd/S1_573_PrimRec.lean'"

def main (args : List String) : IO UInt32 := do
  match args with
  -- The refresh imports every stale module, and `Index.run` reaches it without going through
  -- `refreshedIndex?`, so the split-part guard has to be repeated here.
  | ["index"] => return ← if ← staleSplitParts then pure 1 else Index.run false
  | ["index", "--full"] => return ← if ← staleSplitParts then pure 1 else Index.run true
  -- The child half of the index's syntax-tree pass: elaborate `path`, print its command syntax
  -- tree as `syntax_node` records (cells joined by `fieldSep`, records by `recordSep`) on stdout,
  -- and exit.  Only the index driver calls this; a human running it gets the same records.
  | "syntax-rows" :: path :: _ =>
      let moduleName ← match moduleNameOfPath path with
        | .ok n => pure n
        | .error message => IO.eprintln message; return 2
      let rows ← SyntaxRows.ofFile path (toString moduleName)
      if !rows.nodes.isEmpty then
        IO.print (String.intercalate Db.recordSep rows.nodes.toList)
      return 0
  | ["uses", declName] => return ← usesReport declName
  | ["modularize", "--glob", pattern] => return ← modularizeGlob pattern false
  | ["modularize", "--glob", pattern, "--apply"] => return ← modularizeGlob pattern true
  | ["modularize", path] => return ← modularize path false
  | ["modularize", path, "--apply"] => return ← modularize path true
  -- 200 nodes is about a ten-line proof block: 459 groups on this repository, against 8901 at 40,
  -- where a report is mostly shapes Lean's syntax gives no other spelling.
  | ["dup"] => return ← dupReport 200
  | ["dup", "--min-nodes", nodes] =>
      let some n := nodes.toNat? | IO.eprintln s!"invalid --min-nodes value `{nodes}`"; return 2
      return ← dupReport n
  | ["lint-book-file", path] =>
      return ← lintBookFile path
  | ["lint-book", "--glob", pattern] =>
      return ← forkPerFile pattern fun path => #["lint-book-file", path]
  | ["rename-module", oldModule, newModule] =>
      return ← renameModule oldModule newModule false
  | ["rename-module", oldModule, newModule, "--apply"] =>
      return ← renameModule oldModule newModule true
  | ["move", sourcePath, declName, targetPath] =>
      return ← moveDeclaration sourcePath declName targetPath false
  | ["move", sourcePath, declName, targetPath, "--apply"] =>
      return ← moveDeclaration sourcePath declName targetPath true
  | ["move-into", sourcePath, declName, targetPath, targetNamespace] =>
      return ← moveDeclaration sourcePath declName targetPath false none (some targetNamespace)
  | ["move-into", sourcePath, declName, targetPath, targetNamespace, "--apply"] =>
      return ← moveDeclaration sourcePath declName targetPath true none (some targetNamespace)
  | ["move-omit", sourcePath, declName, targetPath, binders] =>
      return ← moveDeclaration sourcePath declName targetPath false (some binders)
  | ["move-omit", sourcePath, declName, targetPath, binders, "--apply"] =>
      return ← moveDeclaration sourcePath declName targetPath true (some binders)
  | ["relocate-before", sourcePath, declName, anchorName] =>
      return ← relocateDeclarationBefore sourcePath declName anchorName false
  | ["relocate-before", sourcePath, declName, anchorName, "--apply"] =>
      return ← relocateDeclarationBefore sourcePath declName anchorName true
  | ["relocate-before-section", sourcePath, declName, sectionName] =>
      return ← relocateDeclarationBeforeSection sourcePath declName sectionName false
  | ["relocate-before-section", sourcePath, declName, sectionName, "--apply"] =>
      return ← relocateDeclarationBeforeSection sourcePath declName sectionName true
  | ["collapse", sourcePath, declName, replacement] =>
      return ← collapseDeclaration sourcePath declName replacement false
  | ["collapse", sourcePath, declName, replacement, "--apply"] =>
      return ← collapseDeclaration sourcePath declName replacement true
  | ["collapse-drop-call-arg", sourcePath, declName, replacement, index] =>
      let some argIndex := index.toNat?
        | IO.eprintln s!"invalid argument index `{index}`"; return 2
      return ← collapseDeclaration sourcePath declName replacement false (some argIndex)
  | ["collapse-drop-call-arg", sourcePath, declName, replacement, index, "--apply"] =>
      let some argIndex := index.toNat?
        | IO.eprintln s!"invalid argument index `{index}`"; return 2
      return ← collapseDeclaration sourcePath declName replacement true (some argIndex)
  | ["replace-body", sourcePath, declName, replacement] =>
      return ← replaceDeclarationBody sourcePath declName replacement false
  | ["replace-body", sourcePath, declName, replacement, "--apply"] =>
      return ← replaceDeclarationBody sourcePath declName replacement true
  | ["replace-declaration", sourcePath, declName, replacement] =>
      return ← replaceDeclaration sourcePath declName replacement false
  | ["replace-declaration", sourcePath, declName, replacement, "--apply"] =>
      return ← replaceDeclaration sourcePath declName replacement true
  | ["remove-declaration", sourcePath, declName] =>
      return ← removeDeclaration sourcePath declName false
  | ["remove-declaration", sourcePath, declName, "--apply"] =>
      return ← removeDeclaration sourcePath declName true
  | "rename-file" :: path :: rest =>
      let moduleName ← match moduleNameOfPath path with
        | .ok n => pure n
        | .error message => IO.eprintln message; return 2
      let (pairs, apply) := stripApply rest
      match parseRenames pairs with
      | .error message => IO.eprintln message; return 2
      | .ok renames => return ← renameReferences path moduleName renames apply
  | "rename" :: args =>
      -- `--no-index` may appear anywhere in the argument list: it forces the glob driver onto
      -- the per-file elaboration path so the two paths can be diffed against each other.
      let noIndex := args.contains "--no-index"
      let args := args.filter (· != "--no-index")
      match args with
      | "--glob" :: pattern :: rest =>
          let (pairs, apply) := stripApply rest
          match parseRenames pairs with
          | .error message => IO.eprintln message; return 2
          | .ok renames => return ← renameGlob pattern renames apply noIndex
      | path :: moduleName :: rest =>
          let (pairs, apply) := stripApply rest
          match parseRenames pairs with
          | .error message => IO.eprintln message; return 2
          | .ok renames => return ← renameReferences path moduleName renames apply
      | _ => IO.eprintln usage; return 2
  | "rename-decl" :: "--glob" :: pattern :: rest =>
      let (pairs, apply) := stripApply rest
      match parseRenames pairs with
      | .error message => IO.eprintln message; return 2
      | .ok renames => return ← renameDeclGlob pattern renames apply
  | "rename-decl-stage" :: path :: stagePath :: pairs =>
      match parseRenames pairs with
      | .error message => IO.eprintln message; return 2
      | .ok renames => return ← renameDeclStage path stagePath renames
  | ["infix", "--glob", pattern, declName, token] =>
      return ← infixGlob pattern declName token false
  | ["infix", "--glob", pattern, declName, token, "--apply"] =>
      return ← infixGlob pattern declName token true
  | ["infix-stage", path, declName, token, stagePath] =>
      return ← infixStage path declName token stagePath
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
  | ["unused-file", path] =>
      return ← refactorSuggestedWarnings { path } false
  | ["unused-file", path, "--apply"] =>
      return ← refactorSuggestedWarningsUntilStable { path }
  | ["unused", "--glob", pattern] | ["unused", "--glob", pattern, "--apply"] =>
      -- Forked, not looped: an in-process loop retained one `Environment` per file and so died on
      -- the third, on `claimElaboration`'s bound.  This subcommand was unusable above two files.
      let apply := args.getLast? == some "--apply"
      return ← forkPerFile pattern fun path =>
        #["unused-file", path] ++ (if apply then #["--apply"] else #[])
  | ["unused-simp-file", path] | ["unused-simp-file", path, "--apply"] =>
      return ← refactorSuggestedWarnings { path } (args.getLast? == some "--apply")
        (includeVariables := false)
  | ["unused-simp", "--glob", pattern] | ["unused-simp", "--glob", pattern, "--apply"] =>
      let apply := args.getLast? == some "--apply"
      return ← forkPerFile pattern fun path =>
        #["unused-simp-file", path] ++ (if apply then #["--apply"] else #[])
  | _ => pure ()
  let (mode, sourcePath, moduleName, declModule, declName, binderName?, argIndex?, insertText?, token?, apply) ← match args with
    | ["inspect", sourcePath, moduleName, declModule, declName] =>
        pure ("inspect", sourcePath, moduleName, declModule, declName, none, none, none, none, false)
    | ["remove-call-arg", sourcePath, moduleName, declModule, declName, index] =>
        pure ("remove", sourcePath, moduleName, declModule, declName, none, index.toNat?, none, none, false)
    | ["remove-call-arg", sourcePath, moduleName, declModule, declName, index, "--apply"] =>
        pure ("remove", sourcePath, moduleName, declModule, declName, none, index.toNat?, none, none, true)
    | ["remove-call-arg", sourcePath, moduleName, declModule, declName, index, "--syntax"] =>
        pure ("remove-syntax", sourcePath, moduleName, declModule, declName, none, index.toNat?, none, none, false)
    | ["remove-call-arg", sourcePath, moduleName, declModule, declName, index, "--syntax", "--apply"] =>
        pure ("remove-syntax", sourcePath, moduleName, declModule, declName, none, index.toNat?, none, none, true)
    | ["remove-call-arg", sourcePath, moduleName, declModule, declName, index, "--syntax", "--token", token] =>
        pure ("remove-syntax", sourcePath, moduleName, declModule, declName, none, index.toNat?, none, some token, false)
    | ["remove-call-arg", sourcePath, moduleName, declModule, declName, index, "--syntax", "--token", token, "--apply"] =>
        pure ("remove-syntax", sourcePath, moduleName, declModule, declName, none, index.toNat?, none, some token, true)
    | ["remove-call-arg", sourcePath, moduleName, declModule, declName, index, "--token", token] =>
        pure ("remove", sourcePath, moduleName, declModule, declName, none, index.toNat?, none, some token, false)
    | ["remove-call-arg", sourcePath, moduleName, declModule, declName, index, "--token", token, "--apply"] =>
        pure ("remove", sourcePath, moduleName, declModule, declName, none, index.toNat?, none, some token, true)
    | ["insert-call-arg", sourcePath, moduleName, declModule, declName, index, term] =>
        pure ("insert", sourcePath, moduleName, declModule, declName, none, index.toNat?, some term, none, false)
    | ["insert-call-arg", sourcePath, moduleName, declModule, declName, index, term, "--apply"] =>
        pure ("insert", sourcePath, moduleName, declModule, declName, none, index.toNat?, some term, none, true)
    | ["remove-parameter", sourcePath, moduleName, declName, binderName, index] =>
        pure ("parameter", sourcePath, moduleName, moduleName, declName, some binderName, index.toNat?, none, none, false)
    | ["remove-parameter", sourcePath, moduleName, declName, binderName, index, "--apply"] =>
        pure ("parameter", sourcePath, moduleName, moduleName, declName, some binderName, index.toNat?, none, none, true)
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
    if mode != "remove" && mode != "remove-syntax" && mode != "insert" then
      for msg in frontend.commandState.messages.toList do IO.eprintln (← msg.toString)
      return 1
  let commands := frontend.commands
  let ileanPath := System.FilePath.mk ".lake/build/lib/lean" /
    System.FilePath.mk (moduleName.replace "." "/" ++ ".ilean")
  let ilean ← Ilean.load ileanPath
  let mut sites := if mode == "remove-syntax" then #[] else usageSites ilean declModule declName
  if mode == "remove-syntax" then
    for command in frontend.commands do
      sites := sites ++ syntaxSitesNamed inputCtx.fileMap declName command
  if sites.isEmpty && (mode == "remove" || mode == "insert") then
    let refs := Server.findModuleRefs inputCtx.fileMap
      frontend.commandState.infoState.trees.toArray (localVars := false)
    let (liveReferences, _) ← refs.toLspModuleRefs
    sites := usageSitesIn liveReferences declModule declName
    if sites.isEmpty then sites := usageSitesNamed liveReferences declName
    if sites.isEmpty && env.contains (parseName declName) then
      for command in frontend.commands do
        sites := sites ++ syntaxSitesNamed inputCtx.fileMap declName command
  if let some token := token? then
    for command in frontend.commands do
      sites := sites ++ tokenSitesNamed inputCtx.fileMap token command
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
      else editForSite inputCtx.fileMap site commands (oneBased - 1) source
      match result with
      | .error message =>
          -- `--syntax` matches by name, so the declaration's own binder line answers to it and is
          -- not an application: report and carry on rather than abandoning the file.
          unless mode == "remove-syntax" do
            IO.eprintln message
            return 1
          IO.println s!"skipped: {message}"
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
    -- `insert-call-arg` produces a zero-width edit, which spans no text to report as removed; the
    -- preview is the only thing the caller sees before `--apply`, so it must name the real operation.
    for edit in edits do
      if edit.start == edit.stop then
        IO.println s!"line {edit.line}: insert {repr edit.replacement}"
      else
        IO.println s!"line {edit.line}: remove {repr (String.Pos.Raw.extract source edit.start edit.stop)}"
    if apply then
      IO.FS.writeFile sourcePath (applyEdits source edits)
      IO.println s!"applied {edits.size} edit(s) to {sourcePath}"
    else
      IO.println "preview only; pass --apply to write"
  return 0

end LeanRefactor

public def main (args : List String) : IO UInt32 := LeanRefactor.main args
