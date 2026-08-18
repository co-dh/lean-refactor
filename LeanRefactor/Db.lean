module

import Lean
public import Lean.Data.Json

open Lean

namespace LeanRefactor.Db

/-- Field and record separators, matching sqlite3's `--ascii` import mode (0x1F, 0x1E). -/
public def fieldSep : String := "\x1f"
public def recordSep : String := "\x1e"

/-- 0x1D between the two record groups a `syntax-rows` child prints — its syntax nodes, then its
    declaration statements.  One stream and one fork: a second run would re-elaborate the file. -/
public def groupSep : String := "\x1d"

/-- The records of each group a `syntax-rows` child printed.  A child that failed prints nothing,
    and both groups then come back empty rather than as one malformed group. -/
public def childGroups (stdout : String) : Array String × Array String :=
  let records (s : String) : Array String := ((s.splitOn recordSep).filter (· != "")).toArray
  match stdout.splitOn groupSep with
  | [nodes, stmts] => (records nodes, records stmts)
  | _ => (#[], #[])

/-- One row: the cell values joined by `fieldSep`. -/
public def row (cells : Array String) : String :=
  String.intercalate fieldSep cells.toList

/-- Single quotes in a name are escaped by doubling, as SQL string literals require. -/
public def escaped (name : String) : String :=
  name.replace "'" "''"

/-- A hash as a cell.  The mask keeps it below 2^63: SQLite integers are signed 64-bit, and an
    unmasked `UInt64` at or above 2^63 does not survive the import as an integer. -/
public def cell (h : UInt64) : String :=
  toString (h &&& 0x7fffffffffffffff)

/-- The schema version stored in `meta`. Bump when `schemaSql` changes, and also whenever a stored
    column changes MEANING rather than shape.
    `ensureSchema` reacts by deleting the database, and that is the point: a refresh re-extracts only
    the modules whose artefacts changed, so after a keying change the untouched modules would keep
    rows computed by the old algorithm and a grouping query would silently mix two generations. -/
public def schemaVersion : String := "8"

/-- The complete DDL (given below verbatim). -/
public def schemaSql : String :=
"create table meta (key text primary key, value text);

-- `id` is what `syntax_node` stores instead of the name: four million rows carried 70 MB of repeated
-- module names, and the name is 18 characters against an integer's two.  Assigned by the refresh
-- from `max(id) + 1`, never `rowid` — `vacuum` renumbers rowids and would silently repoint every
-- syntax node of every module the refresh did not touch.
create table module (
  id         integer,
  name       text primary key,
  source     text,
  ilean_hash text,
  olean_hash text
);

-- The 434 distinct node kinds, interned for the same reason: 42 MB of repeated `Lean.Parser.…`.
-- Kept as a table rather than folded into a hash, so `select kind, count(*)` still reads.
create table syntax_kind (id integer primary key, name text unique);

create table decl_range (
  name text, module text,
  l1 int, c1 int, l2 int, c2 int,
  sl1 int, sc1 int, sl2 int, sc2 int,
  primary key (name, module)
);

-- `stmt` is the signature as the source spells it, so \"what does this say\" is one query.  The
-- no-token-text rule below is `syntax_node`'s 4.15 M rows; 12 k signatures cost 2 MB against 322.
create table decl_info (
  name text, user_name text, module text,
  kind text,
  internal int,
  stmt text,
  primary key (name, module)
);

create table use_site (
  name        text,
  decl_module text,
  use_module  text,
  l1 int, c1 int, l2 int, c2 int,
  parent      text,
  is_definition int
);

-- `src` names `dst`, and in which face: `in_type` is the declaration's statement — a public one
-- publishes it, and the code generator has to reduce it identically downstream — while `in_value`
-- is the body, which an unexposed declaration keeps to itself.  One row per pair; a constant named
-- in both carries both flags.
create table dep (src text, dst text, module text, in_type int, in_value int);

-- The command-level syntax tree of every indexed module, flattened in preorder.  `id` is the
-- node's index in that order, `parent` the id of the enclosing node (-1 for a root command), so a
-- subtree is a contiguous id range and the innermost node covering byte P is one indexed query.
-- `b0`/`b1` are the node's byte range in its source file; there is no `atom` column — a token's
-- text is `source[b0:b1]`.  `hash` keys the subtree for the duplicate report and `nodes` counts it.
-- Validity is exactly the module's olean validity: the tree is a byproduct of the elaboration that
-- produced the olean, so the same `(ilean_hash, olean_hash)` key and the same delete-and-reinsert
-- path keep it in step with the rest of the index.
--
-- WITHOUT ROWID, keyed by `(module, id)`: the table is then clustered by module, which is how every
-- reader reads it, and the separate module index that cost 119 MB over 4.15 M rows disappears.
-- `hash` gets NO index, deliberately.  A secondary index on a WITHOUT ROWID table repeats the whole
-- primary key in every entry, so indexing `hash` measured 158 MB — more than the index it replaced —
-- while the only query that groups on it also filters on `nodes`, which no index covers, so it scans
-- the table either way.  Measured with the index and without: 0.6 s both times, 192 MB apart.
create table syntax_node (
  module int, id int, parent int, kind int, b0 int, b1 int, hash int, nodes int,
  primary key (module, id)
) without rowid;

-- Where a `syntax-rows` child's output lands, module and kind still spelled out, before the refresh
-- interns both into `syntax_node`.  Staging rather than a wider child protocol: the child prints one
-- module in one process and knows nothing about the ids the database has handed out.
create table syntax_node_in (
  module text, id int, parent int, kind text, b0 int, b1 int, hash int, nodes int
);

-- Where the same child's statements land, keyed by the start of the declaration's name token, until
-- the refresh joins them through `decl_range` onto the mangled name `decl_info` goes by.
create table decl_stmt_in (module text, sl1 int, sc1 int, stmt text);

create index i_use_name   on use_site(name);
create index i_use_module on use_site(use_module);
create index i_dep_dst    on dep(dst);
create index i_dep_src    on dep(src);
create unique index i_module_id on module(id);
-- The statement join's key: a `syntax-rows` child reports positions, and this is what turns one
-- into the name `decl_info` is keyed by.
create index i_decl_range_pos on decl_range(module, sl1, sc1);
"

/-- Spawn `sqlite3` with `extraArgs`, feeding it `sql` from the temp file `tmp` via `.read`.
    `tmp` is chosen by the caller so concurrent runs never share a temp file. -/
private def runSqlite (dbPath : String) (tmp : String) (extraArgs : Array String) (sql : String) : IO String := do
  IO.FS.writeFile tmp sql
  let out ← IO.Process.output { cmd := "sqlite3", args := extraArgs ++ #["-batch", dbPath, ".read " ++ tmp] }
  try IO.FS.removeFile tmp catch _ => pure ()
  if out.exitCode != 0 then
    throw <| IO.userError s!"sqlite3 failed on {dbPath}: {out.stderr}"
  else
    return out.stdout

/-- Run `sql` against the database, creating the file if needed.
    Throws `IO.userError` carrying sqlite3's stderr when sqlite3 exits non-zero. -/
public def exec (dbPath : String) (sql : String) : IO Unit := do
  _ ← runSqlite dbPath (dbPath ++ ".sql.tmp") #[] sql
  pure ()

/-- Run `sql` and return the rows sqlite3 prints in `-json` mode.
    Zero rows: sqlite3 prints nothing, and this must return `Json.arr #[]`, not an error. -/
public def query (dbPath : String) (sql : String) : IO Json := do
  let stdout ← runSqlite dbPath (dbPath ++ ".sql.tmp") #["-json"] sql
  if stdout.isEmpty then
    return Json.arr #[]
  else
    match Json.parse stdout with
    | .ok j => return j
    | .error e => throw <| IO.userError s!"sqlite3 on {dbPath} returned invalid JSON: {e}"

/-- True when the database already carries `schemaVersion` in `meta`.
    Any failure (missing file, missing `meta` table, corrupt db) means not current. -/
private def schemaCurrent (dbPath : String) : IO Bool := do
  try
    let v ← runSqlite dbPath (dbPath ++ ".sql.tmp") #[] "select value from meta where key = 'schema_version';"
    return v.trimAscii.toString == schemaVersion
  catch _ => return false

/-- Apply `schemaSql` when the database is new or its `meta.schema_version` differs from `schemaVersion`.
    Returns `true` when the schema was (re)created, `false` when the existing database was already current.
    Recreating means: delete the database file and start over — this is a derived cache, never a source of truth. -/
public def ensureSchema (dbPath : String) : IO Bool := do
  if (← schemaCurrent dbPath) then
    return false
  else
    try IO.FS.removeFile dbPath catch _ => pure ()
    exec dbPath schemaSql
    exec dbPath "pragma journal_mode = wal;"
    exec dbPath s!"insert into meta (key, value) values ('schema_version', '{schemaVersion}');"
    return true

/-- Bulk-load ASCII-separated `records` into `table`, in one transaction.
    An empty `records` array is a no-op that must not spawn sqlite3.
    Write the records to a temporary file and use `.import --ascii <file> <table>`. -/
public def importRows (dbPath : String) (table : String) (records : Array String) : IO Unit := do
  unless records.isEmpty do
    let rowsTmp := dbPath ++ "." ++ table ++ ".rows.tmp"
    IO.FS.writeFile rowsTmp (String.intercalate recordSep records.toList)
    try
      _ ← runSqlite dbPath (dbPath ++ "." ++ table ++ ".import.tmp") #[] s!".import --ascii {rowsTmp} {table}"
      pure ()
    finally
      try IO.FS.removeFile rowsTmp catch _ => pure ()

end LeanRefactor.Db
