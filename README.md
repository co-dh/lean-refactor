# lean-refactor

Conservative source refactoring for Lean 4 repositories, driven by Lean's own data rather than by text
matching. Two inputs decide every edit:

* `.ilean` reference data — identifies the uses of a global declaration *semantically*;
* the fully elaborated command syntax tree — identifies the enclosing application and its explicit arguments.

An edit is refused if a resolved reference is not an ordinary application, the requested argument is absent, or
the original source range is unavailable. There is no textual fallback. Every operation previews by default and
writes only with `--apply`; the transactional ones re-run the target repository's build afterwards and restore
the original source if it fails.

## Build

```sh
lake build
```

Lean core only — no `require`, no manifest entries, so a clone builds in seconds.

## Use

```sh
cd /path/to/target-repo
lake build                      # the tool reads .ilean, so the target must have been built once
/path/to/lean-refactor/scripts/lean-refactor            # no arguments: list the operations
/path/to/lean-refactor/scripts/lean-refactor rename-decl --glob 'src/*.lean' Foo.old_name new_name
```

Operations cover renaming (uses, binding sites, modules, files, notation tokens), moving declarations between
files and namespaces, relocating them within a file, collapsing a duplicate onto its survivor, replacing a body
or a whole declaration, adding and removing call arguments and parameters, and clearing unused-variable and
unused-`simp`-argument warnings.

**Run it from the target repository's root.** Paths are CWD-relative: the tool loads
`.lake/build/lib/lean/<Module>.ilean` and verifies with `./scripts/cap lake build`, both resolved against the
current directory. `scripts/lean-refactor` deliberately does not `cd` anywhere — it builds the tool in its own
root, then execs the binary under `lake env` in the directory you called it from, which is what supplies the
target's `LEAN_PATH`. Target and tool must be on the same toolchain, or olean loading fails.

Two couplings to the target repository remain, inherited from the repository this was extracted from:

* the post-edit verification shells out to `./scripts/cap lake build`, so the target needs an executable
  `scripts/cap` (a one-line `ulimit -v` wrapper — copy this repository's);
* `lint-book` and `lint-book-file` are lints for a book formalization (`§`-citation ordering, `Freyd.Functor`
  result types, functor-role name suffixes) and mean nothing outside it.

## Why the address-space cap

An unbounded Lean process does not fail politely, it gets OOM-killed, and it takes down whatever else is
running: a `rename --glob` that elaborated file after file in one process reached 18.3 GB resident and killed a
concurrent agent. Two controls came out of that, both kept here — `forkPerFile` gives each file its own child
process, and `scripts/cap` converts a runaway into an immediate attributable failure. The measurements are in
`scripts/cap`.

## Provenance

Extracted from the [freyd](https://github.com/co-dh/freyd) formalization repository, where the tool was written to perform
its own de-duplication passes; the history here is the 32 commits that touched it.
