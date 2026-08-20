# lean-refactor

Conservative, semantic refactoring for Lean 4 repositories. It renames declarations, modules, files
and notation tokens; finds and collapses duplicated source; and answers what a built repository
contains. A **notation token** is the symbol a `notation` or `infixl` command introduces — `≫`, `⊆ₛ`
— as the source literally writes it; it is not a declaration, so nothing in the index knows it by
name.

Every command previews. `--apply` is the one flag that writes; it may sit anywhere in the argument
list. An applied repository-wide edit is verified by a build and restored if that build fails.

Edits come from Lean's own data — `.ilean` reference data says which occurrence is semantically the
declaration, the elaborated syntax tree says its exact range — so an edit the tool cannot establish
is refused rather than guessed at. There is no text-search fallback.

## Build and run

```sh
lake build                                   # once, in this repository
cd /path/to/target-repo
lake build                                   # produces the .ilean data the tool reads
/path/to/lean-refactor/scripts/lean-refactor rename Foo.old new_name
```

Run from the target repository root. The target and this tool must be on the same Lean toolchain.

## Commands

`lean-refactor -h`, inserted verbatim by `scripts/sync-readme` — run it after changing the usage
text so the two cannot drift apart.

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
  tok  a notation token: the symbol a `notation`/`infixl` command introduces, as the source
       literally writes it — `≫`, `⊆ₛ`.  Not a declaration, so the index has no row for it.

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

A command takes the thing it edits and works the rest out: the index says which file declares a
declaration, and whether a name is a declaration, a module, a file or a notation token. The decision
is printed before any edit. A name that is both a module and a declaration is refused rather than
guessed — write the module as its path to say which you meant.

`--in` is the only file selector, and it only narrows.

## Driving it from an agent

Every command previews by default, says what it decided before writing, and refuses rather than
guesses — so the loop is: **ask** (`stmt` for signatures, `uses` for dependents), **preview** (check
the first line: which kind, which file), **apply**, **read the warnings** (leftover textual mentions
the info trees never recorded, and modules that depend through notation without naming anything).

- **Never grep for a declaration.** A private copy's real name is mangled (`_private.Mod.0.Foo`), so
  grep reports a name as unique when it is not. Use `stmt`, or query `decl_info.user_name`.
- **Pass a short replacement, not a qualified one**, or uses inside a file that already opened the
  namespace become `Ns.Ns.name`.
- **Do not name a file** unless the tool reports the name as ambiguous.
- **Batch renames of one kind.** Scanning is the whole cost of a sweep, so `rename a b c d` costs one
  pass where two commands cost two. Mixed kinds are refused.
- **Rebuild after reverting a source by hand**, or the index keeps answering for the edit you undid.
- **No output for minutes means a hung import**, not a slow one — usually orphaned
  `.olean.server`/`.olean.private` parts from a rolled-back build. The tool names the files to delete.

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

`id` is assigned from `max(id) + 1`, never from `rowid`, which `vacuum` renumbers.

### `syntax_kind` — interned parser node kinds

| Column | Type    | Meaning                   | Example                         |
| ------ | ------- | ------------------------- | ------------------------------- |
| `id`   | integer | Interned ID, primary key. | `1`                             |
| `name` | text    | Lean syntax kind, unique. | `Lean.Parser.Command.namespace` |

434 kinds against 4.15 M nodes; interning them saved 42 MB of repeated `Lean.Parser.…`.

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

Query `user_name`: a private copy re-proving a public lemma is invisible under its mangled `name`.

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

The two faces decide what an edit must do: a private constant in a public *statement* is illegal
where the same constant in the *proof* is fine. One row per pair, both flags set if named in both.
Indexed on `src` and `dst`.

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

`WITHOUT ROWID`, clustering by module. `hash` has no index deliberately — adding one measured
158 MB for no speedup, since the query that groups on it also filters on `nodes` and scans anyway.

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

A `syntax-rows` child knows nothing about the IDs the database has handed out, so it writes names
and the refresh interns them.

### `decl_stmt_in` — staging for `decl_info.stmt`

| Column   | Type | Meaning                                     | Example                     |
| -------- | ---- | ------------------------------------------- | --------------------------- |
| `module` | text | Module the signature came from.             | `Freyd.S1_95`               |
| `sl1`    | int  | Start line of the declaration's name token. | `61`                        |
| `sc1`    | int  | Start column of it.                         | `15`                        |
| `stmt`   | text | The signature as the source spells it.      | `{X Y Z : 𝒞} {m : X ⟶ Y} …` |

Keyed by position because the child reports positions; the refresh joins through `decl_range` onto
the mangled name. Indexed for that join as `decl_range(module, sl1, sc1)`.
