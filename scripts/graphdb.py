"""The dependency graph `lean-refactor graph` draws, read back out of the index.

Imported by `svd-layout`, `community` and `concept`, which all three need the same nodes, the same
edges and the same hub cut: a second spelling of any of them would compute an overlay for a graph
the page does not draw.

Run from the repository being indexed — the paths below are relative to it, as the tool's are.
"""
import os
import sqlite3
from collections import Counter

DB = '.lake/build/refactor-index.db'
OUT = 'refactor-graph-%s.tsv'      # beside the page `lean-refactor graph` writes by default
HUB_INDEG = 100                    # the cut in LeanRefactor/Graph.lean; see `hubInDeg` for why


def group(source):
    """A declaration's group: the directory its file is in, as the viewer buckets it."""
    return source.rsplit('/', 1)[0] if '/' in source else '(root)'


def graph(db=DB):
    """(names, sources, edges): index-aligned name and source path per node, edges as index pairs.

    `user_name` on both ends — `dep` stores the mangled name and the page keys on the readable one.
    Declarations the compiler wrote are out, and so is every hub, with its edges.
    """
    if not os.path.exists(db):
        raise SystemExit(f'no {db} in {os.getcwd()} — run this from the repository being indexed, '
                         f'after `lean-refactor index`')
    c = sqlite3.connect(f'file:{db}?mode=ro', uri=True)
    rows = c.execute("""select i.user_name, m.source from decl_info i
        join module m on m.name = i.module where i.internal = 0
        order by m.source, i.user_name""").fetchall()
    eds = c.execute("""select distinct a.user_name, b.user_name from dep d
        join decl_info a on a.name = d.src and a.module = d.module and a.internal = 0
        join decl_info b on b.name = d.dst and b.internal = 0
        where a.user_name != b.user_name""").fetchall()
    c.close()
    if not rows:
        raise SystemExit(f'{db} holds no declarations — run `lean-refactor index --full` first')
    # in-degree over EVERY edge, so what counts as a hub does not depend on what was already dropped
    indeg = Counter(t for _, t in eds)
    idx, names, sources = {}, [], []
    for name, source in rows:
        if indeg[name] > HUB_INDEG or name in idx:
            continue
        idx[name] = len(names)
        names.append(name)
        sources.append(source)
    edges = [(idx[a], idx[b]) for a, b in eds if a in idx and b in idx]
    return names, sources, edges
