module

import Lean
import LeanRefactor.Db
import LeanRefactor.Fork
import LeanRefactor.IleanRows
import LeanRefactor.OleanRows
import LeanRefactor.SyntaxRows

open Lean LeanRefactor.Fork

namespace LeanRefactor.Index

/-- A built module found under `buildDir`: its dotted name (the SQL key), the hierarchical name the
    olean header knows (from the path, exactly as the compiler's `moduleNameOfFileName`), the derived
    source path, the two artifact hashes, and the path of its `.ilean` below `buildDir`. -/
private structure Module where
  name      : String
  srcName   : Name
  source    : String
  ileanHash : String
  oleanHash : String
  relPath   : String

/-- Read `p`, trimmed; a missing file reads as `""`. -/
private def readTrimmed (p : System.FilePath) : IO String := do
  try return (← IO.FS.readFile p).trimAscii.toString catch _ => return ""

/-- The trimmed contents of every existing `X.olean*.hash` file in `dir`, in sorted filename order,
    joined by `,`. Lean 4.28 splits a module into `X.olean`, `X.olean.private` and `X.olean.server`,
    each with its own `.hash`; an ordinary module has only `X.olean.hash`. -/
private def oleanHashes (dir : System.FilePath) (entries : Array IO.FS.DirEntry) (fileBase : String) : IO String := do
  let hashNames := (entries.filter fun e =>
      e.fileName.startsWith (fileBase ++ ".olean") && e.fileName.endsWith ".hash")
    |>.map (·.fileName)
    |>.qsort (· < ·)
  let mut parts := #[]
  for h in hashNames do
    parts := parts.push (← readTrimmed (dir / System.FilePath.mk h))
  return String.intercalate "," parts.toList

/-- Recurse `relDir` ("" for the build root) collecting every `.ilean` as a `Module`.
    A `.ilean` whose module name would be empty is skipped. -/
private partial def scanDir (buildDir relDir : String) : IO (Array Module) := do
  let dir := System.FilePath.mk buildDir / System.FilePath.mk relDir
  let entries ← System.FilePath.readDir dir
  let mut acc := #[]
  for entry in entries do
    if ← entry.path.isDir then
      acc := acc ++ (← scanDir buildDir (relDir ++ entry.fileName ++ "/"))
    else if entry.fileName.endsWith ".ilean" then
      let rel := relDir ++ entry.fileName
      let base := (rel.dropEnd ".ilean".length).toString
      unless base.isEmpty do
        let name := base.replace "/" "."
        let ileanHash ← readTrimmed (dir / System.FilePath.mk (entry.fileName ++ ".hash"))
        let oleanHash ← oleanHashes dir entries ((entry.fileName.dropEnd ".ilean".length).toString)
        acc := acc.push {
          name,
          srcName := (System.FilePath.mk base).components.foldl Name.mkStr Name.anonymous,
          source := name.replace "." "/" ++ ".lean",
          ileanHash, oleanHash, relPath := rel }
  return acc

/-- The `module` table as a map from name to the stored hash pair. -/
private def storedModules (dbPath : String) : IO (Std.HashMap String (String × String)) := do
  let j ← Db.query dbPath "select name, ilean_hash, olean_hash from module;"
  let mut map : Std.HashMap String (String × String) := {}
  match j with
  | .arr rows =>
      for row in rows do
        map := map.insert (row.getObjValAs? String "name" |>.toOption |>.getD "")
          ((row.getObjValAs? String "ilean_hash" |>.toOption |>.getD ""),
           (row.getObjValAs? String "olean_hash" |>.toOption |>.getD ""))
  | _ => pure ()
  return map

/-- The scanned modules whose hash pair differs from the stored pair, plus scanned modules not
    stored at all. -/
private def staleModules (scanned : Array Module) (stored : Std.HashMap String (String × String)) : Array Module :=
  scanned.filter fun m =>
    match stored.get? m.name with
    | none => true
    | some (ileanHash, oleanHash) => ileanHash != m.ileanHash || oleanHash != m.oleanHash

/-- The stored modules the scan no longer found. -/
private def removedModules (scanned : Array Module) (stored : Std.HashMap String (String × String)) : Array String :=
  let scannedNames := scanned.foldl (fun (s : Std.HashSet String) m => s.insert m.name) ∅
  stored.fold (fun acc name _ => if scannedNames.contains name then acc else acc.push name) #[]

/-- Delete every partition row owned by `modules`, in one transaction. Single quotes in a module
    name are escaped by doubling, as SQL string literals require. -/
private def deletePartitions (dbPath : String) (modules : Array String) : IO Unit := do
  unless modules.isEmpty do
    let mut sql := "begin;\n"
    for m in modules do
      let m := m.replace "'" "''"
      sql := sql ++ s!"delete from decl_range where module = '{m}';\n" ++
        s!"delete from decl_info where module = '{m}';\n" ++
        s!"delete from use_site where use_module = '{m}';\n" ++
        s!"delete from dep where module = '{m}';\n" ++
        s!"delete from import_edge where src = '{m}';\n" ++
        -- Before the `module` row it points at, or the id is gone and the nodes are orphans.
        s!"delete from syntax_node where module in (select id from module where name = '{m}');\n" ++
        s!"delete from module where name = '{m}';\n"
    Db.exec dbPath (sql ++ "commit;")

/-- The largest module id the database has handed out, so the refresh can number what it inserts
    from there.  An id never collides with a LIVE module's: a module deleted and re-inserted gets a
    fresh one, which is what keeps the syntax nodes of every module the refresh did NOT touch
    pointing where they did. -/
private def maxModuleId (dbPath : String) : IO Nat := do
  match ← Db.query dbPath "select coalesce(max(id), 0) as m from module;" with
  | .arr rows =>
      if let some row := rows[0]? then return (row.getObjValAs? Nat "m" |>.toOption |>.getD 0)
      return 0
  | _ => return 0

/-- Move one refresh's staged syntax rows into `syntax_node`, interning the module name and the node
    kind on the way.  Both are joins, not lookups the caller could have done: a `syntax-rows` child
    prints one module in one process and knows nothing about the ids this database has handed out. -/
private def internStagedNodes (dbPath : String) : IO Unit :=
  Db.exec dbPath "begin;
insert or ignore into syntax_kind (name) select distinct kind from syntax_node_in;
insert into syntax_node (module, id, parent, kind, b0, b1, hash, nodes)
  select m.id, i.id, i.parent, k.id, i.b0, i.b1, i.hash, i.nodes
  from syntax_node_in i
  join module m on m.name = i.module
  join syntax_kind k on k.name = i.kind;
delete from syntax_node_in;
commit;"

/-- Move one refresh's staged statements onto `decl_info`.  Also a join, and for the same reason:
    the child read the source, so it knows a position, never the `_private.`-mangled name the row
    is keyed by — `decl_range`, keyed by both, is what turns the one into the other. -/
private def attachStatements (dbPath : String) : IO Unit :=
  Db.exec dbPath "begin;
update decl_info set stmt = s.stmt
  from decl_stmt_in s
  join decl_range r on r.module = s.module and r.sl1 = s.sl1 and r.sc1 = s.sc1
  where decl_info.name = r.name and decl_info.module = r.module;
delete from decl_stmt_in;
commit;"

/-- How many modules the `module` table holds — exactly the set the scan found, because every
    stale row is deleted and re-inserted under the same name. -/
private def moduleCount (dbPath : String) : IO Nat := do
  let j ← Db.query dbPath "select count(*) from module;"
  match j with
  | .arr rows =>
      if let some row := rows[0]? then
        return (row.getObjValAs? Nat "count(*)" |>.toOption |>.getD 0)
      return 0
  | _ => return 0

/-- A build directory outlives the sources that produced it: renaming `Fredy` to `Freyd` left 583
    `Fredy/*.ilean` behind in this repository's `.lake`, one of which still imports a package that is
    no longer required, so importing the scan as a whole failed outright.  An artefact whose source
    file is gone is not part of the repository being indexed — it cannot be edited, so nothing that
    reads this index can act on it.  Dropped, never silently: the count is reported. -/
private def withSources (scanned : Array Module) : IO (Array Module × Nat) := do
  let mut kept := #[]
  for m in scanned do
    if ← System.FilePath.pathExists (System.FilePath.mk m.source) then kept := kept.push m
  return (kept, scanned.size - kept.size)

/-- Refresh the index at `dbPath`, scanning `buildDir`. With `full := true`, discard the database first.
    Returns (modules re-extracted, modules dropped, source-less artefacts skipped).

    Each stale module also gets its `syntax_node` rows: the tree is a byproduct of the elaboration
    that built the olean, so the same `(ilean_hash, olean_hash)` key keeps it in step, and the
    DELETE-and-re-insert is the same `deletePartitions` path as every other per-module row. -/
public def refresh (dbPath buildDir : String) (full : Bool) : IO (Nat × Nat × Nat) := do
  if full then
    -- Drop the WAL and SHM too, so a stale write-ahead log cannot be replayed into the fresh file.
    for f in #[dbPath, dbPath ++ "-wal", dbPath ++ "-shm"] do
      try IO.FS.removeFile f catch _ => pure ()
  _ ← Db.ensureSchema dbPath
  let (scanned, orphaned) ← withSources (← scanDir buildDir "")
  let stored ← storedModules dbPath
  let stale := staleModules scanned stored
  let removed := removedModules scanned stored
  deletePartitions dbPath (stale.map (·.name) ++ removed)
  let mut declRanges := #[]
  let mut useSites := #[]
  for m in stale do
    let rows ← IleanRows.ofIlean (System.FilePath.mk buildDir / System.FilePath.mk m.relPath)
    declRanges := declRanges ++ rows.declRanges
    useSites := useSites ++ rows.useSites
  -- ONE import for the whole stale set: the memory rule of this project is one environment per
  -- refresh, never one per module.
  -- One import for the whole batch means one unimportable module takes the batch with it, so say
  -- which repository state caused it rather than letting Lean's bare search-path error surface.
  let oleanRows ← if stale.isEmpty then pure { declInfos := #[], deps := #[], imports := #[] } else
    try OleanRows.ofModules (stale.map (·.srcName))
    catch e => throw <| IO.userError s!"cannot import the modules to index: {e}\n\
      the build directory holds an artefact whose imports no longer resolve; \
      rebuild with `lake build`, or delete the stale artefacts under {buildDir}"
  -- Each module's syntax tree is one full elaboration, so one process must not hold the
  -- environments of many files — measured at 18.3 GB on this repository — and every tree is built
  -- in a CHILD process that prints the flattened rows and exits.  The child is THIS binary, not
  -- `lake exe`: the parent is by construction the up-to-date build.  A failed child prints its
  -- stderr and the module still gets its rows — the semantic rows are the freshness authority, and
  -- a module that `ofModules` just imported cleanly elaborates fine here, so a failure is a broken
  -- build, not a reason to keep the module stale and retry every refresh.
  let self := (← IO.appPath).toString
  let outputs ← mapFilesParallel (← scanJobs) (stale.map (·.source)) fun path =>
    IO.Process.output { cmd := self, args := #["syntax-rows", path] }
  let mut syntaxRows := #[]
  let mut stmtRows := #[]
  for output in outputs do
    let (nodes, stmts) := Db.childGroups output.stdout
    syntaxRows := syntaxRows ++ nodes
    stmtRows := stmtRows ++ stmts
    unless output.stderr.isEmpty do IO.eprint output.stderr
  Db.importRows dbPath "decl_range" declRanges
  Db.importRows dbPath "use_site" useSites
  Db.importRows dbPath "decl_info" oleanRows.declInfos
  Db.importRows dbPath "dep" oleanRows.deps
  Db.importRows dbPath "import_edge" oleanRows.imports
  -- The `module` rows go in BEFORE the syntax nodes that intern their names against them.
  let firstId ← (· + 1) <$> maxModuleId dbPath
  Db.importRows dbPath "module" (stale.mapIdx fun i m =>
    Db.row #[toString (firstId + i), m.name, m.source, m.ileanHash, m.oleanHash])
  Db.importRows dbPath "syntax_node_in" syntaxRows
  Db.importRows dbPath "decl_stmt_in" stmtRows
  internStagedNodes dbPath
  attachStatements dbPath
  -- A full extract stages every module's nodes and then deletes them, which leaves a quarter of a
  -- gigabyte of freed pages the file never gives back on its own.  Only on `full`: an incremental
  -- refresh's freelist is exactly what the NEXT refresh's staging writes into, so compacting it
  -- would trade seconds for pages about to be reallocated.
  if full then Db.exec dbPath "vacuum;"
  return (stale.size, removed.size, orphaned)

/-- `lean-refactor index [--full]`: refresh and print a one-line summary. Returns the process exit code. -/
public def run (full : Bool) : IO UInt32 := do
  let buildDir := ".lake/build/lib/lean"
  unless ← System.FilePath.isDir buildDir do
    IO.eprintln s!"{buildDir} does not exist; run `lake build` first"
    return 1
  let dbPath := ".lake/build/refactor-index.db"
  let t0 ← IO.monoMsNow
  let (reExtracted, dropped, orphaned) ← refresh dbPath buildDir full
  let elapsed := (← IO.monoMsNow) - t0
  let scanned ← moduleCount dbPath
  IO.println s!"indexed {scanned} module(s): {reExtracted} re-extracted, {dropped} dropped, \
    {orphaned} skipped as source-less artefacts, in {elapsed} ms"
  return 0

end LeanRefactor.Index
