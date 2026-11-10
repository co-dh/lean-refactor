module

-- `public` because the signature below is spelled in Lean's own types.
public import Lean
import LeanRefactor.Db

open Lean

namespace LeanRefactor.Elaborate

/-- Why a file's import header could not be used.  `parsed` is false when the header did not even
    parse; `messages` is the log UNPRINTED, so each caller keeps its own reporting. -/
public structure HeaderError where
  parsed : Bool
  messages : MessageLog

/-- `lake setup-file path`, the setup Lake hands the editor for a file no target builds: its last
    line of output is the `ModuleSetup`. -/
private def lakeSetupFile (path : String) (built : System.FilePath) : IO ModuleSetup := do
  let out ← IO.Process.output { cmd := "lake", args := #["setup-file", path] }
  let fail (why : String) : IO ModuleSetup := throw <| IO.userError s!"{path}: {built} does not exist \
    (no build wrote it) and `lake setup-file {path}` {why}; run `lake build` on the module first"
  if out.exitCode != 0 then return ← fail s!"exited {out.exitCode}: {out.stderr.trimAscii}"
  let some line := (out.stdout.splitOn "\n").reverse.find? (·.startsWith "{")
    | fail s!"printed no setup: {out.stdout.trimAscii}"
  match Json.parse line >>= fromJson? with
  | .ok setup => return setup
  | .error e => fail s!"printed a setup that does not parse: {e}"

/-- Every `[name, hash]` pair anywhere in a lake trace: how a trace lists each input it hashed. -/
private partial def hashPairs : Json → Array (String × String)
  | .arr #[.str p, .str h] => #[(p, h)]
  | .arr xs => xs.flatMap hashPairs
  | .obj kvs => kvs.foldl (fun acc _ v => acc ++ hashPairs v) #[]
  | _ => #[]

/-- Refuse a `.lake` that mixes two builds: a library `mainModule`'s trace recorded at its last build
    whose `.hash` now says it was rebuilt since.  A failed or interrupted build leaves exactly that, and
    loading such a set runs native code compiled against another layout of the same structures — a
    segfault in `initialize`, not an error.  A loaded library the trace does not list (an
    `extern_lib`, which lake leaves out of a module's trace) has nothing to compare against. -/
public def checkLibraries (path : String) (mainModule : Name) (setup : ModuleSetup) : IO Unit := do
  let loaded := setup.dynlibs ++ setup.plugins
  if loaded.isEmpty then return
  let trace := mainModule.components.foldl (fun p c => p / c.toString) (System.FilePath.mk Db.buildDir)
    |>.addExtension "trace"
  let fix := s!"run `lake build {mainModule}` (with any declaration edited ahead of a refactor stashed: \
    `git stash; lake build {mainModule}; git stash pop`)"
  unless ← trace.pathExists do
    throw <| IO.userError s!"{path}: {trace} does not exist, so which libraries `{mainModule}` was \
      built against is unknown; {fix}"
  let json ← IO.ofExcept <| (Json.parse (← IO.FS.readFile trace)).mapError (s!"{trace}: " ++ ·)
  let recorded := hashPairs (json.getObjValD "inputs")
  -- Lake's resolution of the workspace NOW: each package's `<root>/.lake/build/lib/lean` on the path.
  let resolved := ((← IO.getEnv "LEAN_PATH").map System.SearchPath.parse |>.getD []).filterMap (·.parent)
  for lib in loaded do
    let some (_, built) := recorded.find? (·.1 == lib.toString) | continue
    -- A `.lake` copied from another tree keeps that tree's library paths in its setups while the
    -- imports read THIS tree's `.olean`s, so this tree's copy of the library must match as well.
    -- A library already where the workspace resolves its package (a `require`d package's own
    -- `.lake`) is the one in use; there is no copy of it under this package's `.lake`.
    let parts := lib.components
    let local? := if lib.parent.any resolved.contains then none
      else parts.findIdx? (· == ".lake") |>.map fun i => System.mkFilePath (parts.drop i)
    let copies := match local? with
      | some l => if l.toString != lib.toString then #[lib, l] else #[lib]
      | none => #[lib]
    for copy in copies do
      let hashFile := copy.toString ++ ".hash"
      unless ← System.FilePath.pathExists hashFile do
        throw <| IO.userError s!"{path}: {hashFile} does not exist, so whether {copy} is the build \
          `{mainModule}` was compiled against is unknown; {fix}"
      let now := (← IO.FS.readFile hashFile).trimAscii.toString
      unless now == built do
        throw <| IO.userError s!"{path}: `{mainModule}` was built against {lib} at hash {built}, but \
          {copy} is at {now}: .lake mixes two builds, and loading the library would run native code \
          compiled against another form of the `.olean`s it is imported with.  {fix}"

/-- The setup lake handed `lean` when it last built `mainModule`: `.lake/build/ir/<M>.setup.json`,
    checked against the libraries on disk.  The last build's and not a fresh `lake setup-file`'s,
    because that one BUILDS the imports first and the tool reads the artefacts on disk as they are;
    only a file no build wrote a setup for (one no target builds) asks `lake setup-file`. -/
public def setupOf (path : String) (mainModule : Name) : IO ModuleSetup := do
  let file := mainModule.components.foldl (fun p c => p / c.toString) (System.FilePath.mk Db.irDir)
    |>.addExtension "setup.json"
  unless ← file.pathExists do return ← lakeSetupFile path file
  let setup ← ModuleSetup.load file
  checkLibraries path mainModule setup
  return setup

/-- Build the environment `header` imports, set up as `lean` sets it up under lake: the module's
    `dynlibs` loaded and its `plugins` handed to the import, so an imported `initialize` that calls
    an `@[extern]` finds the native symbol (without them: "Could not find native implementation of
    external declaration"), and the module's options in force. -/
public def headerEnv (path : String) (header : Elab.HeaderSyntax) (messages : MessageLog)
    (inputCtx : Parser.InputContext) (mainModule : Name) : IO (Environment × MessageLog × Options) := do
  let setup ← setupOf path mainModule
  -- the toolchain's own libraries (Lake's, for a lakefile) are already this process's: loaded again
  -- they register their environment extensions twice
  let sysroot := (← findSysroot).toString
  let theirs (l : System.FilePath) := !l.toString.startsWith sysroot
  (setup.dynlibs.filter theirs).forM Lean.loadDynlib
  let opts := setup.options.toOptions
  let (env, messages) ← Elab.processHeader header opts messages inputCtx
    (plugins := setup.plugins.filter theirs) (mainModule := mainModule)
  return (env, messages, opts)

/-- Parse `source`'s import header, build the environment its imports define, and run the frontend
    over the rest.  Stops there: what a COMMAND error means is the caller's decision, not this one's.
    The environment handed back is the one the IMPORTS built, which is what re-elaborating an edit
    of the same file needs; `frontend.commandState.env` is the one the commands left behind.
    With `stop?`, the commands end after the first that leaves it true of the environment: reading
    one declaration's elaborated form costs the commands up to it, not the whole file. -/
public def frontendOf (path source : String) (mainModule : Name)
    (stop? : Option (Environment → Bool) := none) :
    IO (Except HeaderError (Parser.InputContext × Environment × Elab.Frontend.State)) := do
  let inputCtx := Parser.mkInputContext source path
  let (header, parserState, headerMessages) ← Parser.parseHeader inputCtx
  if headerMessages.hasErrors then return .error { parsed := false, messages := headerMessages }
  let (env, headerMessages, opts) ← headerEnv path header headerMessages inputCtx mainModule
  if headerMessages.hasErrors then return .error { parsed := true, messages := headerMessages }
  let commandState := Elab.Command.mkState env {} opts
  let some stop := stop?
    | return .ok (inputCtx, env, ← Elab.IO.processCommands inputCtx parserState commandState)
  let mut st : Elab.Frontend.State := { commandState, parserState, cmdPos := parserState.pos }
  repeat
    let (done, st') ← (Elab.Frontend.processCommand.run { inputCtx }).run st
    st := st'
    if done || stop st.commandState.env then break
  return .ok (inputCtx, env, st)

end LeanRefactor.Elaborate
