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
# Rename a declaration and every use of it.  Drop --apply to see the edits first.
lean-refactor rename Foo.old_name new_name --apply

# The same command renames a module, a file, or a notation token — the index says which it is.
lean-refactor rename Foo.Bar Foo.Baz            # a module: its file, and every import of it
lean-refactor rename '⊆c' '⊆ₛ'                  # a notation token

# Find repeated source fragments, then read what one of the declarations says.
lean-refactor dup --min-nodes 200
lean-refactor stmt old_name

# See the modules that use a declaration.
lean-refactor uses Foo.bar
```

## Commands

This is `lean-refactor -h`, inserted verbatim by `scripts/sync-readme` — run it after changing the
usage text, so this block and the binary cannot drift apart.

<!-- usage:begin -->

```text
usage: lean-refactor command [args] [--in g] [--apply]

  --apply writes the edit; without it a command only previews.  A repository-wide edit is
  verified by a build and restored if that build fails.

  --in g  which files to work on: one path, a glob, or a comma-list where a leading ! subtracts
          'Lib/Basic.lean' | 'Lib/*.lean' | 'Lib/*.lean,!Lib/Slow.lean'
          Default: the file the index says declares d; the whole repository for the sweeps
          (rename, infix, unused, unused-simp, modularize).

  d  declaration, full name      r  replacement      n  index, counting from 1

query
  index [--full]                          build or refresh the index
  uses d                                  modules that use d
  stmt frag                               signatures of declarations whose name has frag in it
  dup [--min-nodes n]                     repeated source subtrees
  inspect d                               call sites of d

rename
  rename (old r)...                       old is a declaration, a module, a .lean file, or a notation token
    --uses-only                           write r where old is used, but not where it is declared
    --no-index                            find the files by elaborating them, not from the index
  infix d token                           give d the infix notation token

move
  move d dest                             dest is another .lean file, or a declaration or section to sit before
    --into ns                             ... into namespace ns
    --omit binders                        ... omitting binders

replace
  collapse d r                            replace duplicate d by its survivor r
    --drop-arg n                          ... dropping argument n at every call
  replace d text                          replace d entirely
    --body                                ... replace only the body of d
  remove d                                remove d

arguments
  remove-arg d n                          remove argument n at every call of d
    --syntax                              match calls by name where elaboration cannot
    --token tok                           also match calls written as the notation tok
  insert-arg d n term                     insert term before argument n
  remove-param d binder n                 remove a parameter Lean reports unused

cleanup
  unused [f:line:col]                     remove unused binders
  unused-simp                             remove unused `simp` arguments
  modularize                              convert to the Lean module system
```

<!-- usage:end -->

A command takes the thing it edits and works the rest out. Which file declares a declaration comes
from the index; whether a name is a declaration, a module, a file, or a notation token is decided the
same way, and the decision is printed before any edit. A name that is both a module and a declaration
is refused rather than guessed — write the module as its path to say which you meant.

`--in` is the only file selector, and it only ever narrows: it picks which files a repository-wide
command touches, and it resolves the ambiguity when one name is declared in two files.

## Refactoring with an agent

The tool is built for a coding agent to drive: every command previews by default, states what it
decided before it writes, and refuses rather than guesses. That makes a safe loop:

1. **Ask before editing.** `stmt <fragment>` gives the signature and location of every declaration
   whose name matches; `uses <d>` gives the modules that use it, the modules that depend on it
   without naming it (notation, macro expansion — no edit needed there, but they must still
   compile), and the modules that name it without depending on it. Read both before choosing a name.
2. **Preview.** Run the command with no `--apply`. Check the first line: it says which kind the tool
   decided the name is, and which file it resolved to. A wrong kind or a wrong file is visible here,
   for free.
3. **Apply.** Add `--apply`. A single-file edit is gated on that file elaborating; a repository-wide
   edit stages every file, swaps them in at once, and runs one build — any failure restores every
   source. Report the tool's own verdict line rather than re-deriving it.
4. **Read the warnings.** A rename prints leftover textual mentions the info trees never recorded
   (`unfold` arguments, docstrings) and the count of modules that depend without naming. Neither is
   an error; both are places a human should look.

Rules worth encoding in a skill:

- **Never grep for a declaration.** A private copy's real name is mangled (`_private.Mod.0.Foo`), so
  grep misses it and reports a name as unique when it is not. Query the index instead —
  `select user_name, module from decl_info where user_name like '%.<shortname>'` — or use `stmt`.
- **Pass a short replacement, not a qualified one.** Use sites inside a file that already opened the
  namespace would otherwise be rewritten to `Ns.Ns.name`.
- **Do not name a file unless the tool asks.** The index places the declaration. `--in` is for
  narrowing a sweep, and for the one case the tool reports as ambiguous.
- **A command printing nothing for minutes is hung, not slow.** The usual cause is orphaned
  `.olean.server`/`.olean.private` parts from a rolled-back build; the tool guards against this
  before every index refresh and names the files to delete.
- **Batch renames of one kind.** Scanning is the whole cost of a repository-wide pass, so
  `rename a b c d e f` costs one pass where three commands cost three. Mixed kinds are refused.
- **Rebuild after reverting.** Reverting a source by hand leaves the `.olean`/`.ilean` describing
  the edit, and the index then answers for a file that no longer exists that way.

## How the tool decides

The tool combines Lean's `.ilean` reference data (which identifies declarations semantically) with
the fully elaborated command syntax tree (which identifies the exact source range and arguments). Its
SQLite index makes repository-wide renames and queries fast. It refuses edits it cannot establish
safely; there is no text-search fallback.

## SQLite index

`index` writes the derived cache at `.lake/build/refactor-index.db`. It is safe to delete: the next
`index` recreates it. Positions in `decl_range` and `use_site` are zero-based UTF-16 LSP positions;
`syntax_node.b0` and `b1` are byte offsets into the source file. The DDL is `LeanRefactor.Db.schemaSql`.

`meta`, `module`, `syntax_kind`, `decl_range`, `decl_info`, `use_site`, `dep` and `syntax_node`
persist. `syntax_node_in` and `decl_stmt_in` are staging tables, empty between refreshes.

Every row is owned by exactly one module — the one whose artefact produced it — so refreshing a
module is `delete where module = 'M'` and re-insert, with no cross-module invalidation.

### `meta` — schema metadata

| Column  | Type | Meaning                     | Example          |
| ------- | ---- | --------------------------- | ---------------- |
| `key`   | text | Metadata name, primary key. | `schema_version` |
| `value` | text | Its value.                  | `8`              |

### `module` — one row per indexed module

| Column       | Type    | Meaning                                                      | Example                |
| ------------ | ------- | ------------------------------------------------------------ | ---------------------- |
| `id`         | integer | Stable internal ID; `syntax_node` stores this, not the name. | `1`                    |
| `name`       | text    | Lean module name, primary key.                               | `AOP.A6_1_Digits`      |
| `source`     | text    | Repository-relative source path.                             | `AOP/A6_1_Digits.lean` |
| `ilean_hash` | text    | Hash of the module's `.ilean`, for detecting stale rows.     | `52deb1f0…`            |
| `olean_hash` | text    | Hash of its `.olean`, likewise.                              | `872f1ebc…`            |

The ID is assigned from `max(id) + 1`, never from `rowid`: `vacuum` renumbers rowids and would
silently repoint every syntax node of every module the refresh did not touch.

### `syntax_kind` — interned parser node kinds

| Column | Type    | Meaning                   | Example                         |
| ------ | ------- | ------------------------- | ------------------------------- |
| `id`   | integer | Interned ID, primary key. | `1`                             |
| `name` | text    | Lean syntax kind, unique. | `Lean.Parser.Command.namespace` |

434 distinct kinds against 4.15 M nodes: interning them saved 42 MB of repeated `Lean.Parser.…`.
Kept as a table rather than folded into a hash so `select kind, count(*)` still reads.

### `decl_range` — where each declaration sits

| Column   | Type | Meaning                                       | Example                             |
| -------- | ---- | --------------------------------------------- | ----------------------------------- |
| `name`   | text | Declaration name; with `module`, primary key. | `Freyd.effective_of_quotient_cover` |
| `module` | text | Declaring module.                             | `Freyd.S1_95`                       |
| `l1`     | int  | Start line of the whole declaration.          | `53`                                |
| `c1`     | int  | Start column of it.                           | `0`                                 |
| `l2`     | int  | End line of it.                               | `67`                                |
| `c2`     | int  | End column of it.                             | `53`                                |
| `sl1`    | int  | Start line of its name token.                 | `61`                                |
| `sc1`    | int  | Start column of its name token.               | `15`                                |
| `sl2`    | int  | End line of its name token.                   | `61`                                |
| `sc2`    | int  | End column of its name token.                 | `42`                                |

### `decl_info` — what each declaration is and says

| Column      | Type | Meaning                                             | Example                            |
| ----------- | ---- | --------------------------------------------------- | ---------------------------------- |
| `name`      | text | Compiler name, mangled if private; +`module` = key. | `_private.S1_95.0.Freyd.mono_comp` |
| `user_name` | text | De-mangled name — what a person writes.             | `Freyd.mono_comp`                  |
| `module`    | text | Declaring module.                                   | `Freyd.S1_95`                      |
| `kind`      | text | `thm`, `def`, `axiom`, `ind`, or `opaque`.          | `thm`                              |
| `internal`  | int  | `1` for a compiler-written name (`eq_1`, `injEq`).  | `0`                                |
| `stmt`      | text | The signature as the source spells it.              | `{X Y Z : 𝒞} {m : X ⟶ Y} …`        |

De-mangling matters: a private copy re-proving a public lemma is a duplicate no name-grep can see,
and `user_name` is what makes the two comparable.

### `use_site` — every recorded occurrence

| Column          | Type | Meaning                                            | Example               |
| --------------- | ---- | -------------------------------------------------- | --------------------- |
| `name`          | text | The declaration referred to.                       | `Freyd.Subobject.arr` |
| `decl_module`   | text | The module that declares it.                       | `Freyd.S1_51`         |
| `use_module`    | text | The module the occurrence is in.                   | `Freyd.S1_51`         |
| `l1`            | int  | Start line of the occurrence.                      | `29`                  |
| `c1`            | int  | Start column of it.                                | `2`                   |
| `l2`            | int  | End line of it.                                    | `29`                  |
| `c2`            | int  | End column of it.                                  | `5`                   |
| `parent`        | text | The enclosing declaration, empty at command level. | `Freyd.Subobject.le`  |
| `is_definition` | int  | `1` for the binding site, `0` for a use.           | `1`                   |

Indexed on `name` and on `use_module`.

### `dep` — which declaration names which, and in what face

| Column     | Type | Meaning                                  | Example                    |
| ---------- | ---- | ---------------------------------------- | -------------------------- |
| `src`      | text | The declaration that has the dependency. | `Freyd.Subobject.IsEntire` |
| `dst`      | text | The declaration it names.                | `Freyd.Subobject.arr`      |
| `module`   | text | The module `src` belongs to.             | `Freyd.S1_51`              |
| `in_type`  | int  | `1` if named in `src`'s statement.       | `0`                        |
| `in_value` | int  | `1` if named in `src`'s body.            | `1`                        |

The two faces are kept apart because where a constant is named decides what has to be done about it:
a private constant in a public *statement* is illegal while the same constant in the *proof* is fine,
and a definition the code generator compiles must reduce its type identically on both sides of a
module boundary — a demand on the type and on nothing else. One row per pair; a constant named in
both faces carries both flags. Indexed on `src` and on `dst`.

### `syntax_node` — the command syntax tree, flattened

| Column   | Type | Meaning                                                        | Example              |
| -------- | ---- | -------------------------------------------------------------- | -------------------- |
| `module` | int  | `module.id`; with `id`, primary key.                           | `1`                  |
| `id`     | int  | Preorder index in the module; a subtree is a contiguous range. | `0`                  |
| `parent` | int  | Enclosing node's `id`, `-1` for a root command.                | `-1`                 |
| `kind`   | int  | `syntax_kind.id`.                                              | `1`                  |
| `b0`     | int  | Start byte offset in the source file.                          | `1572`               |
| `b1`     | int  | End byte offset; a token's text is `source[b0:b1]`.            | `1605`               |
| `hash`   | int  | Subtree hash, identifiers blanked — the `dup` key.             | `422061742356922016` |
| `nodes`  | int  | Subtree size in nodes.                                         | `3`                  |

`WITHOUT ROWID`, so the table is clustered by module — which is how every reader reads it — and the
separate module index that cost 119 MB over 4.15 M rows disappears. `hash` gets no index
deliberately: on a `WITHOUT ROWID` table a secondary index repeats the whole primary key in every
entry, so indexing it measured 158 MB for no gain — the only query that groups on `hash` also filters
on `nodes`, which no index covers, so it scans either way. Measured with and without: 0.6 s both
times, 192 MB apart.

### `syntax_node_in` — staging for `syntax_node`

| Column   | Type | Meaning                                 | Example                |
| -------- | ---- | --------------------------------------- | ---------------------- |
| `module` | text | Module name, not yet interned to an ID. | `Freyd.S1_95`          |
| `id`     | int  | As in `syntax_node`.                    | `0`                    |
| `parent` | int  | As in `syntax_node`.                    | `-1`                   |
| `kind`   | text | Kind name, not yet interned to an ID.   | `Lean.Parser.Term.app` |
| `b0`     | int  | As in `syntax_node`.                    | `1572`                 |
| `b1`     | int  | As in `syntax_node`.                    | `1605`                 |
| `hash`   | int  | As in `syntax_node`.                    | `422061742356922016`   |
| `nodes`  | int  | As in `syntax_node`.                    | `3`                    |

A `syntax-rows` child elaborates one module in one process and knows nothing about the IDs the
database has handed out, so it writes names and the refresh interns them.

### `decl_stmt_in` — staging for `decl_info.stmt`

| Column   | Type | Meaning                                     | Example                     |
| -------- | ---- | ------------------------------------------- | --------------------------- |
| `module` | text | Module the signature came from.             | `Freyd.S1_95`               |
| `sl1`    | int  | Start line of the declaration's name token. | `61`                        |
| `sc1`    | int  | Start column of it.                         | `15`                        |
| `stmt`   | text | The signature as the source spells it.      | `{X Y Z : 𝒞} {m : X ⟶ Y} …` |

Keyed by position because the child reports positions; the refresh joins through `decl_range` onto
the mangled name `decl_info` goes by. Indexed for that join as `decl_range(module, sl1, sc1)`.
