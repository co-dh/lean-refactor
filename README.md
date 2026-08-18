# lean-refactor

Conservative, semantic refactoring for Lean 4 repositories. Its main jobs are:

- **Rename** declarations, uses, modules, files, and notation tokens.
- **Deduplicate** repeated source subtrees with `dup`, then collapse a chosen copy onto its survivor.
- **Query** a built repository: `stmt` answers what a declaration says; `uses` shows its dependents; `index` refreshes the local index.

Edits are previews unless `--apply` is supplied. Applied repository-wide edits are verified by a build and restored if it fails.

## Build and run

```sh
lake build
cd /path/to/target-repo
lake build                         # produces the .ilean data the tool reads
/path/to/lean-refactor/scripts/lean-refactor <command>
```

Run from the target repository root. The target and this tool must use the same Lean toolchain.

## Examples

```sh
# Rename a declaration and all its binding/use sites.
lean-refactor rename-decl --glob 'src/*.lean' Foo.old_name new_name --apply

# Find repeated source fragments, then inspect declaration statements.
lean-refactor dup --min-nodes 200
lean-refactor stmt name-fragment

# See the modules that use a declaration.
lean-refactor uses Foo.bar
```

## Commands

Prefix each with `lean-refactor`. `--apply` writes changes; otherwise edits are previews. A `--glob`
is comma-separated, and a leading `!` excludes a pattern — for example,
`--glob 'Freyd/*.lean,!Freyd/S1_573_PrimRec.lean'`.

### Find

- `index [--full]` — Build or refresh the repository index.
- `uses <full-declaration-name>` — List modules that use a declaration.
- `stmt <name-fragment>` — Show matching declaration signatures.
- `dup [--min-nodes <n>]` — Report repeated source subtrees.

### Rename

- `rename <source.lean> <module> (<full-declaration-name> <replacement>)... [--apply]` — Rename uses in one file.
- `rename --glob '<pattern>' (<full-declaration-name> <replacement>)... [--apply] [--no-index]` — Rename uses across matching files.
- `rename-decl --glob '<pattern>' (<full-declaration-name> <replacement>)... [--apply]` — Rename uses and declaration binding sites.
- `rename-module <old-module> <new-module> [--apply]` — Rename a module, its file, and imports.
- `rename-token <source.lean> <old-token> <new-token> [--apply]` — Rename a notation token in one file.
- `rename-token --glob '<pattern>' <old-token> <new-token> [--apply]` — Rename a notation token across matching files.
- `infix --glob '<pattern>' <full-declaration-name> <token> [--apply]` — Introduce infix notation for a declaration.

### Move and replace

- `move <source.lean> <full-declaration-name> <target.lean> [--apply]` — Move a declaration to another file.
- `move-into <source.lean> <full-declaration-name> <target.lean> <target-namespace> [--apply]` — Move it into a namespace.
- `move-omit <source.lean> <full-declaration-name> <target.lean> <binders> [--apply]` — Move it while omitting binders.
- `relocate-before <source.lean> <full-declaration-name> <anchor-declaration> [--apply]` — Move it before another declaration.
- `relocate-before-section <source.lean> <full-declaration-name> <section-name> [--apply]` — Move it before a section.
- `collapse <source.lean> <full-declaration-name> <replacement> [--apply]` — Replace a duplicate declaration with its survivor.
- `collapse-drop-call-arg <source.lean> <full-declaration-name> <replacement> <1-based-index> [--apply]` — Collapse while dropping an argument.
- `replace-body <source.lean> <full-declaration-name> <term> [--apply]` — Replace a declaration body.
- `replace-declaration <source.lean> <full-declaration-name> <declaration> [--apply]` — Replace a whole declaration.
- `remove-declaration <source.lean> <full-declaration-name> [--apply]` — Remove a declaration.

### Arguments and cleanup

- `inspect <source.lean> <module> <declaration-module> <full-declaration-name>` — Inspect a declaration's call sites.
- `remove-call-arg <source.lean> <module> <declaration-module> <full-declaration-name> <1-based-index> [--syntax] [--token <notation-token>] [--apply]` — Remove a call argument.
- `insert-call-arg <source.lean> <module> <declaration-module> <full-declaration-name> <before-1-based-index> <term> [--apply]` — Insert a call argument.
- `remove-parameter <source.lean> <module> <full-declaration-name> <binder-name> <1-based-index> [--apply]` — Remove a declaration parameter.
- `unused <source.lean>:<line>:<column> [--apply]` — Remove one unused binder.
- `unused --glob '<pattern>' [--apply]` — Remove unused binders across matching files.
- `unused-simp --glob '<pattern>' [--apply]` — Remove unused `simp` arguments.

### Modules and project lints

- `modularize <source.lean> [--apply]` or `modularize --glob '<pattern>' [--apply]` — Convert files to the Lean module system.
- `lint-book-file <source.lean>` or `lint-book --glob '<pattern>'` — Run the project-specific book lints.

## How it works

The tool combines Lean's `.ilean` reference data (which identifies declarations semantically) with the fully elaborated command syntax tree (which identifies the exact source range and arguments). Its SQLite index makes repository-wide renames and queries fast. It refuses edits it cannot establish safely; there is no text-search fallback.

## SQLite index

`index` writes the derived cache at `.lake/build/refactor-index.db`. It is safe to delete: the next
`index` recreates it. Positions in `decl_range` and `use_site` are zero-based UTF-16 LSP positions;
`syntax_node.b0` and `b1` are byte offsets into the source file.

The persistent tables are `meta`, `module`, `syntax_kind`, `decl_range`, `decl_info`, `use_site`,
`dep`, and `syntax_node`. `syntax_node_in` and `decl_stmt_in` are transient import tables and are
normally empty after indexing.

| Table | Column(s) | Meaning | Example |
| --- | --- | --- | --- |
| `meta` | `key`, `value` | Metadata name and value. | `schema_version`, `8` |
| `module` | `id` | Stable internal module ID. | `3` |
|  | `name`, `source` | Lean module name and source path. | `LeanRefactor.Db`, `LeanRefactor/Db.lean` |
|  | `ilean_hash`, `olean_hash` | Artefact hashes used to detect stale rows. | `"…"`, `"…"` |
| `syntax_kind` | `id`, `name` | Interned parser-node ID and its Lean kind. | `17`, `Lean.Parser.Command.declaration` |
| `decl_range` | `name`, `module` | Compiler declaration name and defining module. | `LeanRefactor.Db.schemaSql`, `LeanRefactor.Db` |
|  | `l1`, `c1`, `l2`, `c2` | Start and end of the whole declaration. | `54`, `0`, `141`, `0` |
|  | `sl1`, `sc1`, `sl2`, `sc2` | Start and end of its name token. | `54`, `11`, `54`, `20` |
| `decl_info` | `name`, `user_name`, `module` | Compiler name, source-facing name, and defining module. | `LeanRefactor.Db.schemaSql`, `schemaSql`, `LeanRefactor.Db` |
|  | `kind`, `internal`, `stmt` | Declaration kind, compiler-generated flag, and source-spelled signature. | `def`, `0`, `def schemaSql : String := …` |
| `use_site` | `name`, `decl_module`, `use_module` | Referenced declaration, its defining module, and module containing the occurrence. | `Nat.add`, `Init.Prelude`, `Example` |
|  | `l1`, `c1`, `l2`, `c2` | Start and end of that occurrence. | `12`, `4`, `12`, `11` |
|  | `parent`, `is_definition` | Enclosing declaration and whether this is its binding site (`1`) rather than a use (`0`). | `Example.total`, `0` |
| `dep` | `src`, `dst`, `module` | Declaration with a dependency, named declaration, and owning module. | `Example.total`, `Nat.add`, `Example` |
|  | `in_type`, `in_value` | Dependency is in the statement or body (`0`/`1`). | `0`, `1` |
| `syntax_node` | `module`, `id`, `parent` | `module.id`, preorder node ID, and enclosing node (`-1` for a root). | `3`, `42`, `17` |
|  | `kind` | `syntax_kind.id`. | `17` |
|  | `b0`, `b1` | Source byte range. | `108`, `131` |
|  | `hash`, `nodes` | Normalized subtree hash and subtree size. | `531842`, `12` |
| `syntax_node_in` | `module`, `id`, `parent`, `kind`, `b0`, `b1`, `hash`, `nodes` | Name-based staging form of `syntax_node`; cleared after import. | `Example`, `42`, `17`, `Lean.Parser.Term.app`, `108`, `131`, `531842`, `12` |
| `decl_stmt_in` | `module`, `sl1`, `sc1`, `stmt` | Staged signature, keyed by the declaration-name start; cleared after import. | `Example`, `4`, `4`, `theorem total : …` |
