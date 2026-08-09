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
    for whatever else is running.  `LEAN_REFACTOR_JOBS` overrides it. -/
public def scanJobs : IO Nat := do
  match (← IO.getEnv "LEAN_REFACTOR_JOBS").bind (·.toNat?) with
  | some jobs => pure (max jobs 1)
  | none => pure 12

/-- Run `job` on every path, `jobs` at a time, and return the results IN INPUT ORDER.

    The paths are dealt round-robin into `jobs` buckets, largest file first, and one task drains each
    bucket.  Largest first because the run cannot finish before its longest file does, and a 5 s file
    picked up last sets the floor for everything.  Buckets rather than a shared work queue because a
    bucket is private to its task: an `IO.Ref` counter shared across tasks would be a data race.
    Results carry their input index, so the report stays in glob order however the workers finish and
    two runs of the same command stay diffable. -/
public def mapFilesParallel {α : Type} (jobs : Nat) (paths : Array String)
    (job : String → IO α) : IO (Array α) := do
  let mut sized := #[]
  for index in [0:paths.size] do
    let path := paths[index]!
    sized := sized.push ((← (System.FilePath.mk path).metadata).byteSize, index, path)
  let order := sized.qsort fun left right => left.1 > right.1
  let mut buckets : Array (Array (Nat × String)) := Array.replicate (max jobs 1) #[]
  for position in [0:order.size] do
    let (_, index, path) := order[position]!
    let bucket := position % buckets.size
    buckets := buckets.set! bucket (buckets[bucket]!.push (index, path))
  let tasks ← buckets.mapM fun bucket => IO.asTask do
    let mut done := #[]
    for (index, path) in bucket do done := done.push (index, ← job path)
    pure done
  let mut collected := #[]
  for task in tasks do collected := collected ++ (← IO.ofExcept task.get)
  pure <| (collected.qsort fun left right => left.1 < right.1).map (·.2)

end LeanRefactor.Fork
