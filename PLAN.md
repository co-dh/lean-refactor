# Plan — a SQLite index over `.ilean` and `.olean`, updated per module

The index never *decides* anything. It only narrows which files the existing conservative machinery opens: every
edit is still produced from the elaborated syntax tree and verified by the same build as today. A wrong index can
therefore make the tool slow or make it refuse, but it must never make it write a wrong edit.

## Why

Measured on the freyd repository (226 `Freyd/*.lean`, 1099 built modules, 24 cores), preview only:

| Operation                                              | today                        | SQLite query |
| ------------------------------------------------------ | ---------------------------- | ------------ |
| `rename-decl --glob 'Freyd/*.lean' Cat.assoc …`         | **52.09 s**, peak 3.25 GB    | **2.2 ms**   |
| `rename-decl --glob 'Freyd/*.lean' Freyd.kp_sq …`       | **10.01 s**                  | **0.1 ms**   |

The 52 s is not spent narrowing the candidate set — the `mentioning` prefilter admits 171 files and 167 modules
genuinely reference `Cat.assoc`, so it is already near-optimal. The 52 s is spent **recomputing what `lake build`
already computed and wrote to `.ilean`**. That is the redundancy this plan removes.

A throwaway prototype (`scratchpad/index.py`, not part of this repo) loaded all 1099 `.ilean` into SQLite in
**0.93 s** → 721,840 use sites, 28,549 decls, 98.6 MB with a naive schema.

### Why both artifacts, not just `.ilean`

They cover disjoint halves of the same question, and each is blind exactly where the other sees:

* `.ilean` has **positions but not semantics**. `Freyd/S1_45.lean` writes `≫` 248 times; `≫` is notation for
  `Cat.comp`; `S1_45.ilean` contains **zero** `Cat.comp` entries, because macro-expanded identifiers are synthetic
  and carry no source range.
* `.olean` has **semantics but not positions**. The same file's `kp_sq` yields the edge `kp_sq → Cat.comp` from
  `ci.type.getUsedConstants ++ ci.value?.getUsedConstants` — the data `#print axioms` walks. No line numbers.

So `.olean` answers *which files can break if I change X* (complete: notation, instances, macro output), and
`.ilean` answers *where in those files to type*. Refactoring needs both.

The `.olean` bytes themselves are never stored. An olean is already the fastest possible store — a compacted
region mmap'd at a fixed base address with no deserialization pass. A BLOB would only add a copy.

## The invariant that makes incremental updates trivial

> Every row is owned by exactly one module: the module whose artifact produced it.

* A `.ilean` for module `M` holds `M`'s declaration ranges and the references occurring **in** `M`.
* An `.olean` for `M` holds `M`'s own constants; every dependency edge it yields has its source in `M`.

Therefore updating `M` is `DELETE FROM <table> WHERE module = 'M'` followed by re-inserting `M`'s rows. There is no
cross-module invalidation to reason about, because no row is ever attributable to two modules.

An edge's *target* may name a constant in another module. If that module changes, the edge does not: the string is
still what `M` said. A dangling target is a true fact about a broken build, not an index defect.

## Schema

```sql
create table meta (key text primary key, value text);   -- schema_version, ilean_format_version, built_at

create table module (
  name       text primary key,   -- 'Freyd.S1_45'
  source     text,               -- 'Freyd/S1_45.lean', derived from the name
  ilean_hash text,
  olean_hash text
);

-- One producer per table, so the partitioned delete never has two writers for one row.
create table decl_range (                  -- from .ilean
  name text, module text,
  l1 int, c1 int, l2 int, c2 int,          -- whole declaration, including its docstring
  sl1 int, sc1 int, sl2 int, sc2 int,      -- the name itself (selection range)
  primary key (name, module)               -- NOT name alone: orphan modules can define the same name
);

create table decl_info (                   -- from .olean
  name text, module text,
  kind text,                               -- thm | def | axiom | ind | opaque
  type_key integer,                        -- statement hash; equal keys are duplicate candidates
  primary key (name, module)
);

create table use_site (                    -- from .ilean references
  name        text,                        -- fully qualified constant
  decl_module text,                        -- module that defines it
  use_module  text,                        -- module the occurrence is in  == the owning module
  l1 int, c1 int, l2 int, c2 int,          -- 0-based LSP positions, columns in UTF-16 units
  parent      text,                        -- enclosing declaration, or null
  is_definition int                        -- 1 = binding site, 0 = use. rename moves uses;
);                                         --   rename-decl moves both. The distinction is the operation.

create table dep (src text, dst text, module text);   -- module = owner of src, for the partitioned delete

create index i_use_name   on use_site(name);
create index i_use_module on use_site(use_module);
create index i_dep_dst    on dep(dst);             -- blast radius: who depends on X
create index i_dep_src    on dep(src);
create index i_decl_key   on decl_info(type_key);  -- duplicate detection
```

`type_key` starts as a plain hash of the statement. Alpha/universe normalisation (freyd's `declKey`) is what makes
equal keys mean *duplicate*, and it belongs with the consumer that needs it — not in the first indexer.

Names are stored as repeated TEXT. Interning them into a `name(id, text)` table would cut size several-fold, but it
complicates the partitioned delete (orphaned name rows) and 110 MB of derived cache is not a problem worth paying
for yet. Revisit only if measurement says so.

The database lives at `.lake/build/refactor-index.db` **of the target repository**: beside the artifacts it derives
from, wiped by `lake clean`, already covered by the `/.lake` gitignore. It is a cache, never a source of truth.

## Producers

**`.ilean` → rows.** Pure JSON, no Lean environment, parallelisable per file. Use the package's existing
`Ilean.load` — a second parser for the same format is the duplication this repo bans.

**`.olean` → rows.** Requires Lean. After `importModules`, `env.header.moduleData[i]` gives module `i`'s own
`constNames`/`constants` directly, so per-module extraction needs no filtering by name prefix. For each constant:
`kind`, `type_key`, and `getUsedConstants` of type and value.

This pass builds **one environment in one process** — the sanctioned shape. The OOM lesson behind `forkPerFile` was
one environment *per file in a loop*; a single import of the changed modules' closure is the opposite of that. A
batch of changed modules is one import, not one import each.

Orphan modules (not reachable from the root aggregator) may define colliding constant names, so they cannot share
an environment: group them separately, one environment per orphan group.

## Transport into SQLite

Shell out to `sqlite3` (3.53.4 present at `/usr/bin/sqlite3`). The tool already shells out for verification builds,
and Lean has no SQLite binding in a zero-dependency package; FFI to `libsqlite3` via `extern_lib` is a possible
later optimisation, not a starting point.

Feed rows with `.mode ascii` (0x1F field / 0x1E record separators) and `.import`, **not** CSV. Lean names contain
`«»`, unicode subscripts, and commas; ASCII-separated mode sidesteps quoting entirely.

Read back with `sqlite3 -json` and parse with `Lean.Json`. A query is milliseconds; process spawn is noise against a
52 s baseline.

Concurrency: WAL mode. The `index` command is the only writer. `forkPerFile` children are readers.

## Incremental refresh

```
lean-refactor index [--full] [--no-refresh]
```

1. **Staleness scan.** Read `<module>.ilean.hash` and `<module>.olean.hash` (16 hex chars each) for every built
   module — 1099 files × 16 bytes, milliseconds. Compare against the `module` table. Yields `added`, `changed`,
   `removed`.
2. **Delete.** For each module in `changed ∪ removed`: one `DELETE … WHERE module = ?` per table.
3. **Re-extract.** `.ilean` rows for `added ∪ changed`, in parallel. `.olean` rows for `added ∪ changed`, in one
   process importing their union closure.
4. **Insert** in a single transaction, then update `module` hashes and `meta.built_at`.

`meta.schema_version` and `meta.ilean_format_version` (currently 5) are checked first; a mismatch forces `--full`
rather than a silent misread.

### Refresh policy — the safety-critical part

The read path refreshes automatically: the staleness scan is cheap enough that there is no reason to answer from a
stale index. `--no-refresh` exists as an escape hatch for benchmarking.

**A module in the glob that has no fresh index row is an error, not an empty result.** The tool's ethos is to refuse
rather than guess; an index that silently omits an unbuilt module turns "no uses found" into a wrong rename. If a
selected source file has no built `.ilean`, say so and exit non-zero, naming the file and the fix (`lake build`).

## Phases

**Phase 0 — measure and settle the two unknowns. DONE.**

(a) A full index of freyd — 495 modules, both halves — takes **2.5 s**, and an unchanged re-scan **13 ms**. The
database is 147 MB: 12,335 declaration ranges, 303,333 use sites, 28,104 declarations, 541,427 edges. Against the
52.09 s that a repository-wide rename spends locating its sites, the whole index costs less than one twentieth of
one such run.

(b) The `.hash` files are **per-artefact content hashes**, not trace hashes of inputs. Two measurements: `touch`
plus a rebuild changes no hash and re-extracts nothing, and a real edit to one module re-extracts exactly that
module — its downstream cone stays valid. So incremental never degrades toward full, and the fallback of hashing
artefact bytes ourselves is unnecessary.

**Phase 1 — indexer, no behaviour change. DONE.** `lean-refactor index [--full]` builds and refreshes the
database. Nothing else reads it yet.
*Exit criterion, met:* full build, then a real edit to one module, refresh incrementally, then full rebuild — all
five tables identical modulo row order, and reverting the edit removes the rows again. A `touch` is not a test:
it changes no content, so it changes no hash and exercises nothing.

Two things the real repository taught, both now in the code:

* An artefact whose source file is gone is skipped and counted, never silently dropped. freyd's `.lake` held 583
  `Fredy/*.ilean` from an old rename, one of which still imported a package the repository no longer requires.
* The `.olean` half reads each module's file directly rather than importing a batch into one environment. An
  environment cannot hold two modules that each declare `main` and are never imported together, and importing
  needs every transitive import to resolve. Reading has neither failure mode and needs no search path.

**Phase 2 — the find phase reads the index. DONE for `rename`.** Measured on freyd, preview, byte-identical
output in both cases:

| `rename --glob 'Freyd/*.lean'` | elaborating (`--no-index`) | index      | report          |
| ------------------------------ | -------------------------- | ---------- | --------------- |
| `Cat.assoc`                    | 52.5 s                     | **7.0 s**  | 6847 lines, identical |
| `Freyd.kp_sq`                  | 9.9 s                      | **0.28 s** | 79 lines, identical   |

The stated 1 s target holds for a narrow rename and not for a wide one, and the reason is a deliberate choice:
**the file set is unchanged**. The textual prefilter still selects the candidates, and a candidate for which the
index reports no use site keeps the old path — because a file can name a declaration in a place the info trees do
not record (`unfold`'s arguments), and the syntax fallback that catches those needs the elaboration. For
`Cat.assoc` that is about sixteen of the 171 candidates, and they are the whole of the remaining 7 s. Skipping
them would be faster and would change what the tool reports; that trade is not this phase's to make.

Why the index may stand in for the elaboration at all, for `rename` and only for `rename`: with
`withDefinition := false` the syntax pass in `renameEdits` runs *only* when the semantic pass found nothing, and
the semantic pass reads `Server.findModuleRefs … (localVars := false)` — the very call whose output Lean writes
into the `.ilean`. So in a file where the index reports a site, the two agree by construction. `rename-decl` runs
the syntax pass unconditionally and keeps the old path entirely.

*The freshness guard.* A source edited but not rebuilt has an unchanged `.ilean` whose positions have moved, and
the staleness scan cannot see it — nothing about the artefact changed. A file therefore takes the fast path only
when its `.ilean` is at least as new as its source. Verified: `touch` on a source is enough to send that file back
to the elaboration path, with identical output.

*`--apply` keeps the old path.* Applying re-elaborates to verify the result, so the elaboration the fast path
skips is needed anyway. `--no-index` forces the old path everywhere; it exists so the two can be diffed.

Elaboration does **not** disappear from these operations. `rename-decl` still needs the syntax pass: a `structure`
or `class` field used by the laws declared beside it is a *binder* reference, not a `.const`, so info trees — and
therefore the index — do not record it. What changes is that the syntax pass runs on the handful of files the index
named, not on every file whose text happens to contain the short name.

**Phase 3 — the capabilities the index adds.**
* *Blast radius.* `select distinct module from dep where dst = ?` — the file
  set that can stop compiling. Drives verification scope, so a local change need not trigger a whole-repository
  build.
* *Notation-backed renames.* Today a constant reached only through notation has no recorded use sites, so the token
  pass runs over a textual glob. `dep(dst)` gives the exact module list first.

## Non-goals

* Storing `.olean` bytes. See above.
* Removing the syntax pass. The index has no positions for notation sites and no record of structure-field binders.
* Making the database a source of truth, versioning it, or sharing it between machines. It is derived and
  disposable.
* Retiring freyd's `scripts/ExtractGraph.lean` and its `graph/*.tsv` (118,231 edges, 8,604 decls). Its consumers
  (`dep_dup.py`, `community.py`, `concept.py`) want columns this schema does not yet carry. Revisit once `type_key`
  and the decl metadata are in place; not part of this work.
* Any target-specific naming. Nothing in the schema, the code, or the CLI may mention a particular library — the
  `lint-book` precedent, in reverse.
