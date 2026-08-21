"""The dependency graph `lean-refactor graph` draws, read back out of the index.

The nodes, the edges and the hub cut are the index's own `graph_node` and `graph_edge` views, which
the page reads too — this module no longer defines any of them, it only turns them into the
index-aligned form `svd-layout`, `community` and `concept` all three want.

Run from the repository being indexed — the paths below are relative to it, as the tool's are.
"""
import os
import sqlite3

DB = '.lake/build/refactor-index.db'
OUT = 'refactor-graph-%s.tsv'      # beside the page `lean-refactor graph` writes by default


def group(source):
    """A declaration's group: the directory its file is in, as the viewer buckets it.

    Also spelled as `dirOf` in `viz.html`; a view to share one line of string-splitting would cost
    more than the two copies do.
    """
    return source.rsplit('/', 1)[0] if '/' in source else '(root)'


def graph(db=DB):
    """(names, sources, edges): index-aligned name and source path per node, edges as index pairs.

    Straight off the views: `graph_node` has already dropped the compiler's declarations and every
    hub, and fixed the order the indices below are handed out in.
    """
    if not os.path.exists(db):
        raise SystemExit(f'no {db} in {os.getcwd()} — run this from the repository being indexed, '
                         f'after `lean-refactor index`')
    c = sqlite3.connect(f'file:{db}?mode=ro', uri=True)
    rows = c.execute('select n, s from graph_node').fetchall()
    eds = c.execute('select s, t from graph_edge').fetchall()
    c.close()
    if not rows:
        raise SystemExit(f'{db} holds no declarations — run `lean-refactor index --full` first')
    idx, names, sources = {}, [], []
    for name, source in rows:
        idx[name] = len(names)
        names.append(name)
        sources.append(source)
    edges = [(idx[a], idx[b]) for a, b in eds if a in idx and b in idx]
    return names, sources, edges
