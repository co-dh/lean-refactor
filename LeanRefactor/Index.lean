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

/-- Read `p`, trimmed.  A missing hash file is an error, never `""`: an empty hash stored and an
    empty hash scanned compare equal, so the module would count as up to date forever. -/
private def readTrimmed (p : System.FilePath) : IO String := do
  return (← IO.FS.readFile p).trimAscii.toString

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

/-- The directories below `dir` that hold a lakefile of their own: nested lake packages.  Their
    modules resolve through THEIR `.lake`, so the root's search path cannot elaborate them; each is a
    target of its own, reached with `-C <dir>`, and `index` reaches it by a child under its `lake env`. -/
public partial def nestedPackages (dir : System.FilePath := ".") : IO (Array System.FilePath) := do
  let mut out := #[]
  for entry in ← dir.readDir do
    if entry.fileName.startsWith "." || !(← entry.path.isDir) then continue
    if (← (entry.path / "lakefile.lean").pathExists) || (← (entry.path / "lakefile.toml").pathExists) then
      out := out.push (System.mkFilePath (entry.path.components.filter (· != ".")))
    out := out ++ (← nestedPackages entry.path)
  return out

/-- The innermost nested package (from `nestedPackages`) whose tree holds `path`, compared by path
    component.  Innermost, because a package nested in a nested package owns its own files. -/
public def packageOf (packages : Array System.FilePath) (path : String) : Option System.FilePath :=
  let parts (p : System.FilePath) := p.components.filter (· != ".")
  packages.foldl (init := none) fun best pkg =>
    if (parts path).take (parts pkg).length == parts pkg &&
        best.all (fun b => (parts b).length < (parts pkg).length) then some pkg else best

/-- The `module` table as a map from name to the stored hash pair, restricted to the rows whose
    source is `owned` by the package being refreshed: one database holds every package of the
    repository, and a refresh must neither re-extract nor drop another package's modules. -/
private def storedModules (dbPath : String) (owned : String → Bool) :
    IO (Std.HashMap String (String × String)) := do
  -- A module whose extraction failed keeps its row with no hashes recorded (NULL); '' matches no
  -- scanned hash, so it reads as stale and the next run retries it, as the failure report promises.
  let sql := "select name, source, coalesce(ilean_hash, '') as ilean_hash, \
    coalesce(olean_hash, '') as olean_hash from module;"
  let .arr rows ← Db.query dbPath sql | throw <| IO.userError s!"{dbPath}: `{sql}` did not return an array"
  let mut map : Std.HashMap String (String × String) := {}
  for row in rows do
    let field (k : String) : IO String := match row.getObjValAs? String k with
      | .ok v => pure v
      | .error e => throw <| IO.userError s!"{dbPath}: module row {row.compress}: column {k}: {e}"
    if owned (← field "source") then
      map := map.insert (← field "name") (← field "ilean_hash", ← field "olean_hash")
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
        s!"delete from src_ref where module = '{m}';\n" ++
        s!"delete from open_ns where module = '{m}';\n" ++
        -- Before the `module` row it points at, or the id is gone and the nodes are orphans.
        s!"delete from syntax_node where module in (select id from module where name = '{m}');\n" ++
        s!"delete from module where name = '{m}';\n"
    Db.exec dbPath (sql ++ "commit;")

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

/-- Write the hash pair of each of `modules`, in one transaction: the last write of a refresh, so a
    module counts as up to date only once every row of it is in. -/
private def recordHashes (dbPath : String) (modules : Array Module) : IO Unit := do
  unless modules.isEmpty do
    Db.exec dbPath <| modules.foldl (init := "begin;\n") (fun sql m =>
      sql ++ s!"update module set ilean_hash = '{Db.escaped m.ileanHash}', olean_hash = \
        '{Db.escaped m.oleanHash}' where name = '{Db.escaped m.name}';\n") ++ "commit;"

/-- The runtime's fixed line when an allocation fails (`lean_internal_panic_out_of_memory`).  The
    exit code is a plain 1, so this line is the only thing that tells an OOM from any other failure. -/
private def oomPanic : String := "INTERNAL PANIC: out of memory"

/-- Why a `syntax-rows` child that exited nonzero produced no rows, naming the memory cap when the
    runtime ran out of memory under it.  `scripts/cap` exports `CAP_MEM_MB`, the limit it set. -/
private def childCause (o : IO.Process.Output) : IO String := do
  let code := if o.exitCode > 128 then s!"was killed by signal {o.exitCode - 128}" else s!"exited {o.exitCode}"
  unless (o.stderr.splitOn "\n").any (·.trimAscii.toString == oomPanic) do
    return s!"the `syntax-rows` child {code}; its stderr is above"
  match ← IO.getEnv "CAP_MEM_MB" with
  | some mb => return s!"the `syntax-rows` child ran out of memory under scripts/cap's address-space \
      limit of {mb} MB (`ulimit -v`); raise it: `CAP_MEM_MB=<more than {mb}> lean-refactor index`"
  | none => return s!"the `syntax-rows` child ran out of memory with no scripts/cap limit in effect \
      (CAP_MEM_MB unset): the machine's memory or an outer `ulimit -v` was exhausted"

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
    DELETE-and-re-insert is the same `deletePartitions` path as every other per-module row.

    `me` is the package being refreshed, as a directory relative to the repository root (`none` for
    the root itself), and `packages` every nested package of that root: the refresh owns exactly the
    stored modules whose source `packageOf` places in `me`, and stores its sources root-relative, so
    one database answers for every package of the repository. -/
public def refresh (dbPath buildDir : String) (full : Bool) (packages : Array System.FilePath)
    (me : Option System.FilePath) : IO (Nat × Nat × Nat) := do
  let pre := (me.map (·.toString ++ "/")).getD ""
  if full then
    -- Drop the WAL and SHM too, so a stale write-ahead log cannot be replayed into the fresh file.
    for f in #[dbPath, dbPath ++ "-wal", dbPath ++ "-shm"] do Db.removeIfPresent f
  _ ← Db.ensureSchema dbPath
  let (scanned, orphaned) ← withSources (← scanDir buildDir "")
  let stored ← storedModules dbPath fun source => packageOf packages source == me
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
  -- `lake exe`: the parent is by construction the up-to-date build.  A child that dies leaves its
  -- module without hashes, so the next refresh retries it, and the refresh throws naming it.
  let self := (← IO.appPath).toString
  let outputs ← mapFilesParallel (← scanJobs) (stale.map (·.source)) fun path =>
    tryCatch (IO.Process.output { cmd := self, args := #["syntax-rows", path] }) fun e =>
      throw <| IO.userError s!"{path}: cannot spawn the `syntax-rows` child: {e}"
  let mut groups : Array (Array String) := Array.replicate Db.childGroupCount #[]
  let mut failed : Array (String × String) := #[]
  for (m, output) in stale.zip outputs do
    unless output.stderr.isEmpty do IO.eprint output.stderr
    let parsed ← if output.exitCode == 0 then pure (Db.childGroups output.stdout)
      else Except.error <$> childCause output
    match parsed with
    | .ok gs => groups := (groups.zip gs).map fun (a, b) => a ++ b
    | .error cause => failed := failed.push (m.name, cause)
  let syntaxRows := groups[0]!
  let stmtRows := groups[1]!
  Db.importRows dbPath "decl_range" declRanges
  Db.importRows dbPath "use_site" useSites
  Db.importRows dbPath "decl_info" oleanRows.declInfos
  Db.importRows dbPath "dep" oleanRows.deps
  Db.importRows dbPath "import_edge" oleanRows.imports
  -- The `module` rows go in BEFORE the syntax nodes that intern their names against them, but with
  -- EMPTY hashes: the hashes are what marks a module up to date, so `recordHashes` writes them last,
  -- and a write that fails anywhere before it leaves every module stale.
  -- Numbering from the largest id ever handed out, not from the row count: a module deleted and
  -- re-inserted must get a fresh id, or the untouched modules' syntax nodes point at the wrong one.
  let firstId ← (· + 1) <$> Db.queryNat dbPath "select coalesce(max(id), 0) as m from module;" "m"
  Db.importRows dbPath "module" (stale.mapIdx fun i m => Db.row #[toString (firstId + i), m.name, pre ++ m.source, "", ""])
  Db.importRows dbPath "syntax_node_in" syntaxRows
  Db.importRows dbPath "decl_stmt_in" stmtRows
  Db.importRows dbPath "src_ref" groups[2]!
  Db.importRows dbPath "open_ns" groups[3]!
  internStagedNodes dbPath
  attachStatements dbPath
  let failedNames := failed.foldl (fun (s : Std.HashSet String) (n, _) => s.insert n) ∅
  recordHashes dbPath (stale.filter (!failedNames.contains ·.name))
  unless failed.isEmpty do
    throw <| IO.userError <| String.intercalate "\n" <|
      (failed.map fun (n, cause) => s!"{n}: {cause}").toList ++
      [s!"{failed.size} of {stale.size} module(s) failed extraction; their hashes are not recorded, \
        so the next `lean-refactor index` retries them"]
  return (stale.size, removed.size, orphaned)

/-- Refresh the modules of one package (`me`, `none` for the root) into `dbPath` and print a
    one-line summary naming the package. -/
private def refreshPackage (dbPath : String) (full : Bool) (packages : Array System.FilePath)
    (me : Option System.FilePath) : IO Unit := do
  let t0 ← IO.monoMsNow
  let (reExtracted, dropped, orphaned) ← refresh dbPath Db.buildDir full packages me
  let elapsed := (← IO.monoMsNow) - t0
  let sql := "select source from module;"
  let .arr rows ← Db.query dbPath sql | throw <| IO.userError s!"{dbPath}: `{sql}` did not return an array"
  let mut owned := 0
  for r in rows do
    match r.getObjValAs? String "source" with
    | .ok s => if packageOf packages s == me then owned := owned + 1
    | .error e => throw <| IO.userError s!"{dbPath}: module row {r.compress}: column source: {e}"
  IO.println s!"{(me.map toString).getD "."}: indexed {owned} module(s): {reExtracted} re-extracted, \
    {dropped} dropped, {orphaned} skipped as source-less artefacts, in {elapsed} ms"
  -- Before the next package's child writes to the same stream, so the lines keep their order.
  (← IO.getStdout).flush

/-- `lean-refactor index [--full] [-K key=value]…`: refresh the root package, then every nested lake
    package of the repository into the SAME database, and print a summary line per package.  Returns
    the process exit code.

    A nested package's modules import through ITS search path (its own `.lake` and requirements), so
    each is refreshed by a child of this binary under that package's `lake env`, one package at a
    time — one Lean environment per process.  `lakeArgs` (`-K key=value`) go to that `lake`, for a
    lakefile whose dependency paths are configuration options.  The child inherits `scripts/cap`'s
    limit, and the lock the launcher holds on this database. -/
public def run (full : Bool) (lakeArgs : Array String) : IO UInt32 := do
  unless ← System.FilePath.isDir Db.buildDir do
    IO.eprintln s!"{Db.buildDir} does not exist; run `lake build` first"
    return 1
  let dbPath := Db.indexPath
  let packages ← nestedPackages
  refreshPackage dbPath full packages none
  let root ← IO.currentDir
  let self := (← IO.appPath).toString
  let mut status : UInt32 := 0
  for pkg in packages do
    -- Not an error: a fresh checkout or worktree has not built every package, and failing would
    -- block every index of the root.  Said, with the command that fixes it, never skipped silently.
    unless ← (pkg / Db.buildDir).isDir do
      IO.eprintln s!"{pkg}: nested lake package not built ({pkg}/{Db.buildDir} missing), so its \
        modules keep the rows of its last index; build it with `lake -d {pkg} build`, then rerun \
        `lean-refactor index`"
      continue
    let args := lakeArgs ++ #["env", self, "index-package", (root / dbPath).toString, pkg.toString] ++
      packages.map toString
    let out ← IO.Process.output { cmd := "lake", args, cwd := some pkg }
    unless out.stdout.isEmpty do IO.print out.stdout
    unless out.stderr.isEmpty do IO.eprint out.stderr
    if out.exitCode != 0 then
      IO.eprintln s!"{pkg}: `lake {" ".intercalate (lakeArgs ++ #["env"]).toList} lean-refactor \
        index-package` exited {out.exitCode}; its stderr is above.  A dependency path its lakefile \
        reads from a configuration option is passed as `lean-refactor index -K key=value`"
      status := out.exitCode
  -- A full extract stages every module's nodes and then deletes them, which leaves a quarter of a
  -- gigabyte of freed pages the file never gives back on its own.  Only on `full`: an incremental
  -- refresh's freelist is exactly what the NEXT refresh's staging writes into, so compacting it
  -- would trade seconds for pages about to be reallocated.
  if full then Db.exec dbPath "vacuum;"
  return status

/-- `lean-refactor index-package DB PKG PACKAGES…`, the child half of `run`: run in the nested package
    `PKG` under its `lake env`, refresh its modules into the root's database `DB`. -/
public def runPackage (dbPath : String) (me : System.FilePath) (packages : Array System.FilePath) :
    IO UInt32 := do
  unless ← System.FilePath.isDir Db.buildDir do
    IO.eprintln s!"{me}/{Db.buildDir} does not exist; run `lake build` in {me} first"
    return 1
  refreshPackage dbPath false packages (some me)
  return 0

end LeanRefactor.Index
