# lean-refactor

Conservative, semantic refactoring for Lean 4 repositories. Its main jobs are:

- **Rename** a declaration everywhere it is mentioned, and modules, files, and notation tokens with it.
- **Deduplicate** repeated source subtrees with `dup`, then collapse a chosen copy onto its survivor.
- **Query** a built repository: `stmt` answers what a declaration says; `uses` shows its dependents; `index`
  refreshes the local index.

Every command previews. `--apply` is the one flag that writes, it means the same thing everywhere, and it may sit
anywhere in the argument list. An applied repository-wide edit is verified by a build and restored if that build fails.

## Build and run

```sh
lake build
cd /path/to/target-repo
lake build                         # produces the .ilean data the tool reads
/path/to/lean-refactor/scripts/lean-refactor command [args]
```

Run from the target repository root. The target and this tool must use the same Lean toolchain.

## Examples

```sh
# Rename a declaration and all its binding/use sites.  Drop --apply to see the edits first.
lean-refactor rename-decl --glob 'src/*.lean' Foo.old_name new_name --apply

# Find repeated source fragments, then read what one of the declarations says.
lean-refactor dup --min-nodes 200
lean-refactor stmt old_name

# See the modules that use a declaration.
lean-refactor uses Foo.bar
```

## Commands

This is `lean-refactor` with no arguments:

```text
usage: lean-refactor command [args] [--apply]

  --apply writes the edit; without it a command only previews.  A repository-wide edit is
  verified by a build and restored if that build fails.

  f  source file          d  declaration, full name    n  index, counting from 1
  m  module of f          r  replacement               M  module that declares d
  g  --glob pattern, comma-separated, a leading ! subtracts: 'Freyd/*.lean,!Freyd/S1_573.lean'

query
  index [--full]                          build or refresh the index
  uses d                                  modules that use d
  stmt frag                               signatures of declarations whose name has frag in it
  dup [--min-nodes n]                     repeated source subtrees
  inspect f m M d                         call sites of d
  lint-book-file f | lint-book --glob g   project book lints

rename
  rename f m (d r)...                     write r where f mentions d, but not where d is declared
  rename-file f (d r)...                  the same, with m read from the path of f
  rename --glob g (d r)...                write r where any file matching g mentions d
    --no-index                            find those files by elaborating them, not from the index
  rename-decl --glob g (d r)...           the same, and rename d where it is declared
  rename-module m r                       rename module m to r: its file, and every import of it
  rename-token f old new                  write the notation token new where f writes old
  rename-token --glob g old new           the same, in every file matching g
  infix --glob g d token                  give d the infix notation token

move
  move f d to.lean                        move d to another file
  move-into f d to.lean ns                ... into namespace ns
  move-omit f d to.lean binders           ... omitting binders
  relocate-before f d anchor              move d before another declaration
  relocate-before-section f d section     move d before a section

replace
  collapse f d r                          replace duplicate d by its survivor r
  collapse-drop-call-arg f d r n          ... dropping argument n at every call
  replace-body f d term                   replace the body of d
  replace-declaration f d text            replace d entirely
  remove-declaration f d                  remove d

arguments
  remove-call-arg f m M d n               remove argument n at every call of d
    --syntax                              match calls by name where elaboration cannot
    --token tok                           also match calls written as the notation tok
  insert-call-arg f m M d n term          insert term before argument n
  remove-parameter f m d binder n         remove a parameter Lean reports unused

cleanup
  unused f:line:col                       remove one unused binder
  unused --glob g                         remove unused binders
  unused-simp --glob g                    remove unused `simp` arguments
  modularize f | modularize --glob g      convert to the Lean module system
```

`m` and `M` differ only when the call sites being edited sit in another file than the declaration: `m` is the module
of the file being edited, `M` the one that declares `d`.

## How it works

The tool combines Lean's `.ilean` reference data (which identifies declarations semantically) with the fully elaborated
command syntax tree (which identifies the exact source range and arguments). Its SQLite index makes repository-wide
renames and queries fast. It refuses edits it cannot establish safely; there is no text-search fallback.

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
