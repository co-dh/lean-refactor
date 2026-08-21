module

import Lean
import LeanRefactor.Query

open Lean

namespace LeanRefactor.Graph

/-- In-degree above which a declaration is a HUB and leaves the graph, taking its edges with it.
    Composition, equality and the like are named by nearly everything, so drawn they bury every
    other edge; `scripts/svd-layout` and `scripts/concept` cut at the same floor for the same
    reason. -/
private def hubInDeg : Nat := 100

/-- The viewer, still holding the `__REPO__` and `__GRAPH_DATA__` markers, read at RUN time from the
    tool's own checkout.  Not `include_str`: nothing traces that input, so every edit to the page
    after the first built "successfully" while the binary kept serving the old one. -/
private def page : IO String := do
  -- `.lake/build/bin/lean-refactor` — three levels up is the checkout the page lives in.
  let exe ← IO.appPath
  let some root := exe.parent >>= (·.parent) >>= (·.parent) >>= (·.parent)
    | throw <| IO.userError s!"cannot locate the lean-refactor checkout from {exe}"
  let path := root / "LeanRefactor" / "viz.html"
  unless ← path.pathExists do
    throw <| IO.userError s!"the viewer template is missing: {path}"
  IO.FS.readFile path

/-- A JSON string cell.  `<` is escaped: the data is inlined in a `<script>` element, and the HTML
    parser ends that element at the first `</script` however deep inside a string literal it sits. -/
private def cell (s : String) : String := (Json.str s).compress.replace "<" "\\u003c"

/-- One `decls` row, in the order the page reads it. -/
private def nodeRow (n : Query.GraphNode) : String :=
  "[" ++ cell n.name ++ "," ++ cell n.kind ++ "," ++ cell n.source ++ "," ++ toString n.line ++
    "," ++ cell n.stmt ++ "]"

/-- A JSON array of already-rendered elements, written straight to the file: there are hundreds of
    thousands of them, and joining them into one string would copy that string per element. -/
private def putArray (h : IO.FS.Handle) (rows : Array String) : IO Unit := do
  h.putStr "["
  let mut sep := ""
  for r in rows do
    h.putStr sep
    h.putStr r
    sep := ","
  h.putStr "]"

/-- The rows of an optional sidecar TSV, each as a JSON array of its cells.  `scripts/svd-layout`,
    `scripts/community` and `scripts/concept` write these beside the page; absent is the normal case
    and the page then names the script that would produce what it is missing. -/
private def sidecar (path : System.FilePath) : IO (Array String) := do
  unless ← path.pathExists do return #[]
  let text ← IO.FS.readFile path
  return (text.splitOn "\n").toArray.filterMap fun line =>
    if line.isEmpty then none
    else some ("[" ++ String.intercalate "," ((line.splitOn "\t").map cell) ++ "]")

/-- What the page draws: the nodes that survive the hub cut, the edges among them as index pairs
    into those nodes, and how many hubs were cut.  In-degree is counted over EVERY edge, so what
    counts as a hub does not depend on what has already been dropped. -/
private def selected (nodes : Array Query.GraphNode) (edges : Array (String × String)) :
    Array Query.GraphNode × Array (Nat × Nat) × Nat := Id.run do
  let mut indeg : Std.HashMap String Nat := {}
  for (_, dst) in edges do indeg := indeg.insert dst (indeg.getD dst 0 + 1)
  let mut index : Std.HashMap String Nat := {}
  let mut hubs : Std.HashSet String := ∅
  let mut kept : Array Query.GraphNode := #[]
  for n in nodes do
    if indeg.getD n.name 0 > hubInDeg then
      hubs := hubs.insert n.name
    -- One name declared in two modules is one node, and the edges of both meet on it.
    else if !index.contains n.name then
      index := index.insert n.name kept.size
      kept := kept.push n
  let pairs := edges.filterMap fun (s, t) => do
    let a ← index[s]?
    let b ← index[t]?
    pure (a, b)
  return (kept, pairs, hubs.size)

/-- `lean-refactor graph`: the dependency graph as one self-contained page, the data inlined, so
    there is nothing to serve and nothing to regenerate alongside it.  Returns what the page ended
    up holding — nodes, edges, hubs left out. -/
public def write (dbPath outPath repo : String) : IO (Nat × Nat × Nat) := do
  let (kept, pairs, hubs) := selected (← Query.graphNodes dbPath) (← Query.graphEdges dbPath)
  let dir := (System.FilePath.mk outPath).parent.getD "."
  let side (what : String) : IO (Array String) :=
    sidecar (dir / ("refactor-graph-" ++ what ++ ".tsv"))
  let (before, after) ← match ((← page).replace "__REPO__" repo).splitOn "__GRAPH_DATA__" with
    | [before, after] => pure (before, after)
    | _ => throw <| IO.userError "LeanRefactor/viz.html no longer holds exactly one __GRAPH_DATA__"
  IO.FS.withFile outPath .write fun h => do
    h.putStr before
    h.putStr ("{\"repo\":" ++ cell repo ++ ",\"hubDeg\":" ++ toString hubInDeg ++
      ",\"hubs\":" ++ toString hubs ++ ",\"decls\":")
    putArray h (kept.map nodeRow)
    -- Two entries per edge rather than a pair per edge: at this many edges the brackets are the file.
    h.putStr ",\"deps\":"
    putArray h (pairs.map fun (a, b) => toString a ++ "," ++ toString b)
    h.putStr ",\"pos\":"
    putArray h (← side "pos")
    h.putStr ",\"comm\":"
    putArray h (← side "communities")
    h.putStr ",\"concept\":"
    putArray h (← side "concepts")
    h.putStr "}"
    h.putStr after
  return (kept.size, pairs.size, hubs)

end LeanRefactor.Graph
