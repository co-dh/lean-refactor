module

import Lean

namespace LeanRefactor.Fork

/-- How many child scans run at once.

    A scan is a full Lean elaboration, and `scripts/cap`'s rlimit is PER PROCESS, so it does not
    bound the aggregate of a parallel driver — keeping the total within the machine is this number's
    job.  Measured over the 171 scans of `rename-decl --glob 'Freyd/*.lean' Cat.assoc …`, against
    24 cores and 32 GB: 6 workers 73.7 s, 12 workers 52.3 s, 20 workers 48.9 s, with available
    memory falling by 3.3, 4.2 and 5.7 GB respectively.  Twelve is the knee — past it the run is
    bounded by its few heaviest files, not by how many run at once — and it leaves half the machine
    for whatever else is running.  Re-measured with the shared work queue on a 31-file rename:
    12 workers 8.2 s, 24 workers 9.0 s — the heaviest file still bounds the run, so following the
    core count buys nothing and doubles the aggregate memory.  `LEAN_REFACTOR_JOBS` overrides it. -/
public def scanJobs : IO Nat := do
  match (← IO.getEnv "LEAN_REFACTOR_JOBS").bind (·.toNat?) with
  | some jobs => pure (max jobs 1)
  | none => pure 12

/-- Run `job` on every path, `jobs` at a time, and return the results IN INPUT ORDER.

    One shared queue, largest file first: each worker takes the next file the moment it is free.
    Largest first because the run cannot finish before its longest file does; a queue rather than
    round-robin buckets because a bucket fixed in advance leaves a worker idle while another still
    holds three files — measured at 6.7 busy cores of 12 on a 76-file rename.  The queue is one
    counter taken with `modifyGet`, which the runtime does as an atomic take-then-set, so two
    workers never get the same position.  A worker is a dedicated thread that only waits on its
    child process: the Lean environment lives in the child, one per file, never shared.
    Results carry their input index, so the report stays in glob order however the workers finish and
    two runs of the same command stay diffable. -/
public def mapFilesParallel {α : Type} (jobs : Nat) (paths : Array String)
    (job : String → IO α) : IO (Array α) := do
  let mut sized := #[]
  for index in [0:paths.size] do
    let path := paths[index]!
    sized := sized.push ((← (System.FilePath.mk path).metadata).byteSize, index, path)
  let order := (sized.qsort fun left right => left.1 > right.1).map fun (_, index, path) => (index, path)
  let next ← IO.mkRef 0
  let tasks ← (Array.range (min (max jobs 1) order.size)).mapM fun _ => IO.asTask (prio := .dedicated) do
    let mut done := #[]
    repeat
      let position ← next.modifyGet fun n => (n, n + 1)
      let some (index, path) := order[position]? | break
      done := done.push (index, ← job path)
    pure done
  let mut collected := #[]
  for task in tasks do collected := collected ++ (← IO.ofExcept task.get)
  pure <| (collected.qsort fun left right => left.1 < right.1).map (·.2)

end LeanRefactor.Fork
