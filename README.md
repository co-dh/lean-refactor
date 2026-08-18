# lean-refactor

Conservative, semantic refactoring for Lean 4 repositories. Its main jobs are:

- **Rename** declarations, uses, modules, files, and notation tokens.
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
/path/to/lean-refactor/scripts/lean-refactor <command>
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
usage: lean-refactor <command> [args...] [--apply]

  --apply writes the edit; without it a command only previews.  A repository-wide edit is
  verified by a build and restored if that build fails.

  <file> source path            <decl> full declaration name    <n>     1-based index
  <mod>  module name            <new>  replacement name         <term>  Lean term
  <pat>  glob, comma-separated, a leading `!` subtracts: --glob 'Freyd/*.lean,!Freyd/S1_573.lean'

find
  index [--full]                                   build or refresh the index
  uses <decl>                                      modules that use a declaration
  stmt <frag>                                      signatures of declarations matching <frag>
  dup [--min-nodes <n>]                            repeated source subtrees
  inspect <file> <mod> <decl-mod> <decl>           call sites of a declaration
  lint-book-file <file> | lint-book --glob <pat>   project book lints

rename
  rename <file> <mod> (<decl> <new>)...            uses, in one file
  rename-file <file> (<decl> <new>)...             uses, in one file, module taken from the path
  rename --glob <pat> (<decl> <new>)...            uses, across files [--no-index]
  rename-decl --glob <pat> (<decl> <new>)...       uses and binding sites, across files
  rename-module <old> <new>                        a module, its file, and every import of it
  rename-token <file> <old> <new>                  a notation token, in one file
  rename-token --glob <pat> <old> <new>            a notation token, across files
  infix --glob <pat> <decl> <token>                give a declaration infix notation

move
  move <file> <decl> <to.lean>                     move a declaration to another file
  move-into <file> <decl> <to.lean> <ns>           ... into a namespace
  move-omit <file> <decl> <to.lean> <binders>      ... omitting binders
  relocate-before <file> <decl> <anchor>           move it before another declaration
  relocate-before-section <file> <decl> <section>  move it before a section

replace
  collapse <file> <decl> <new>                     replace a duplicate declaration by its survivor
  collapse-drop-call-arg <file> <decl> <new> <n>   ... dropping argument <n> at every call
  replace-body <file> <decl> <term>                replace a declaration body
  replace-declaration <file> <decl> <text>         replace a whole declaration
  remove-declaration <file> <decl>                 remove a declaration

arguments
  remove-call-arg <file> <mod> <decl-mod> <decl> <n> [--syntax] [--token <token>]
  insert-call-arg <file> <mod> <decl-mod> <decl> <n> <term>   insert before argument <n>
  remove-parameter <file> <mod> <decl> <binder> <n>           remove a parameter Lean reports unused

cleanup
  unused <file>:<line>:<col>                       remove one unused binder
  unused --glob <pat>                              remove unused binders
  unused-simp --glob <pat>                         remove unused `simp` arguments
  modularize <file> | modularize --glob <pat>      convert to the Lean module system
```

`<decl-mod>` is the module that *defines* the declaration, `<mod>` the module being edited; they differ only when the
call sites are in another file. `--syntax` matches call sites by name where elaboration cannot resolve them, and
`--token <token>` also matches its notation.

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
