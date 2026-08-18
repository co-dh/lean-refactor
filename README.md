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

Prefix each command below with `lean-refactor`.

```text
# Build or refresh the repository index (`--full` rebuilds it).
index [--full]
# List modules that use a declaration.
uses <full-declaration-name>
# Show matching declaration signatures.
stmt <name-fragment>
# Report repeated source subtrees.
dup [--min-nodes <n>]
# Convert files to the Lean module system.
modularize <source.lean> [--apply]
modularize --glob '<pattern>' [--apply]
# Run project-specific book lints.
lint-book-file <source.lean>
lint-book --glob '<pattern>'
# Rename a module, its file, and imports.
rename-module <old-module> <new-module> [--apply]
# Move a declaration to another file or namespace.
move <source.lean> <full-declaration-name> <target.lean> [--apply]
move-into <source.lean> <full-declaration-name> <target.lean> <target-namespace> [--apply]
move-omit <source.lean> <full-declaration-name> <target.lean> <binders> [--apply]
# Reposition a declaration within its file.
relocate-before <source.lean> <full-declaration-name> <anchor-declaration> [--apply]
relocate-before-section <source.lean> <full-declaration-name> <section-name> [--apply]
# Replace a duplicate declaration with its survivor.
collapse <source.lean> <full-declaration-name> <replacement> [--apply]
collapse-drop-call-arg <source.lean> <full-declaration-name> <replacement> <1-based-index> [--apply]
# Replace or remove a declaration.
replace-body <source.lean> <full-declaration-name> <term> [--apply]
replace-declaration <source.lean> <full-declaration-name> <declaration> [--apply]
remove-declaration <source.lean> <full-declaration-name> [--apply]
# Rename uses only, or uses and the declaration binding site.
rename <source.lean> <module> (<full-declaration-name> <replacement>)... [--apply]
rename --glob '<pattern>' (<full-declaration-name> <replacement>)... [--apply] [--no-index]
rename-decl --glob '<pattern>' (<full-declaration-name> <replacement>)... [--apply]
# Rename notation tokens or introduce infix notation for a declaration.
rename-token <source.lean> <old-token> <new-token> [--apply]
rename-token --glob '<pattern>' <old-token> <new-token> [--apply]
infix --glob '<pattern>' <full-declaration-name> <token> [--apply]
# Remove unused binders or unused `simp` arguments.
unused <source.lean>:<line>:<column> [--apply]
unused --glob '<pattern>' [--apply]
unused-simp --glob '<pattern>' [--apply]
# Inspect call sites, or remove/insert arguments and parameters.
inspect <source.lean> <module> <declaration-module> <full-declaration-name>
remove-call-arg <source.lean> <module> <declaration-module> <full-declaration-name> <1-based-index> [--syntax] [--token <notation-token>] [--apply]
insert-call-arg <source.lean> <module> <declaration-module> <full-declaration-name> <before-1-based-index> <term> [--apply]
remove-parameter <source.lean> <module> <full-declaration-name> <binder-name> <1-based-index> [--apply]

# A glob is comma-separated; `!` excludes a pattern.
--glob 'Freyd/*.lean,!Freyd/S1_573_PrimRec.lean'
```

## How it works

The tool combines Lean's `.ilean` reference data (which identifies declarations semantically) with the fully elaborated command syntax tree (which identifies the exact source range and arguments). Its SQLite index makes repository-wide renames and queries fast. It refuses edits it cannot establish safely; there is no text-search fallback.
