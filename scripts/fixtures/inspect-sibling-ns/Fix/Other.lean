import Fix.Base

-- `GD` is a namespace SIBLING of `CL` (both live under `Fix`), reached only through `open` — the
-- exact shape of the freyd bug: `rel/AutoDeriveGreedyDP.lean`'s `GreedyDP` used `RelSet.CL.est_pt`
-- through `open GD`/`open CL` and the single-file `inspect` never looked at this file at all.
namespace Fix.GD
open Fix.CL

theorem bar (n : Nat) : n = n := foo n

end Fix.GD
