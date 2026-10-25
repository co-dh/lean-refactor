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

/-- The setup lake handed `lean` when it last built `mainModule`: `.lake/build/ir/<M>.setup.json`.
    The last build's and not a fresh `lake setup-file`'s, because that one BUILDS the imports first,
    and the tool reads the artefacts on disk as they are — a declaration edited ahead of a refactor
    must not be rebuilt under the files still being read against its old form. -/
public def setupOf (path : String) (mainModule : Name) : IO ModuleSetup := do
  let file := mainModule.components.foldl (fun p c => p / c.toString) (System.FilePath.mk Db.irDir)
    |>.addExtension "setup.json"
  unless ← file.pathExists do
    throw <| IO.userError s!"{path}: {file} does not exist, so lake has not built `{mainModule}` and \
      the dynamic libraries its imports need are unknown; run `lake build {mainModule}` first"
  ModuleSetup.load file

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
  for lib in loaded do
    let some (_, built) := recorded.find? (·.1 == lib.toString) | continue
    let hashFile := lib.toString ++ ".hash"
    unless ← System.FilePath.pathExists hashFile do
      throw <| IO.userError s!"{path}: {hashFile} does not exist, so whether {lib} is the build \
        `{mainModule}` was compiled against is unknown; {fix}"
    let now := (← IO.FS.readFile hashFile).trimAscii.toString
    unless now == built do
      throw <| IO.userError s!"{path}: `{mainModule}` was built against {lib} at hash {built}, but \
        that library has been rebuilt since (now {now}): .lake mixes two builds, and loading it would \
        run native code compiled against the other one.  {fix}"

/-- Build the environment `header` imports, set up as `lean` sets it up under lake: the module's
    `dynlibs` loaded and its `plugins` handed to the import, so an imported `initialize` that calls
    an `@[extern]` finds the native symbol (without them: "Could not find native implementation of
    external declaration"), and the module's options in force. -/
public def headerEnv (path : String) (header : Elab.HeaderSyntax) (messages : MessageLog)
    (inputCtx : Parser.InputContext) (mainModule : Name) : IO (Environment × MessageLog × Options) := do
  let setup ← setupOf path mainModule
  checkLibraries path mainModule setup
  setup.dynlibs.forM Lean.loadDynlib
  let opts := setup.options.toOptions
  let (env, messages) ← Elab.processHeader header opts messages inputCtx
    (plugins := setup.plugins) (mainModule := mainModule)
  return (env, messages, opts)

/-- Parse `source`'s import header, build the environment its imports define, and run the frontend
    over the rest.  Stops there: what a COMMAND error means is the caller's decision, not this one's.
    The environment handed back is the one the IMPORTS built, which is what re-elaborating an edit
    of the same file needs; `frontend.commandState.env` is the one the commands left behind. -/
public def frontendOf (path source : String) (mainModule : Name) :
    IO (Except HeaderError (Parser.InputContext × Environment × Elab.Frontend.State)) := do
  let inputCtx := Parser.mkInputContext source path
  let (header, parserState, headerMessages) ← Parser.parseHeader inputCtx
  if headerMessages.hasErrors then return .error { parsed := false, messages := headerMessages }
  let (env, headerMessages, opts) ← headerEnv path header headerMessages inputCtx mainModule
  if headerMessages.hasErrors then return .error { parsed := true, messages := headerMessages }
  let frontend ← Elab.IO.processCommands inputCtx parserState (Elab.Command.mkState env {} opts)
  return .ok (inputCtx, env, frontend)

/-- `frontendOf`, but stopping after the first command that leaves `stop` true of the environment:
    reading one declaration's elaborated form costs the commands up to it, not the whole file. -/
public def envThrough (path source : String) (mainModule : Name) (stop : Environment → Bool) :
    IO (Except HeaderError Environment) := do
  let inputCtx := Parser.mkInputContext source path
  let (header, parserState, headerMessages) ← Parser.parseHeader inputCtx
  if headerMessages.hasErrors then return .error { parsed := false, messages := headerMessages }
  let (env, headerMessages, opts) ← headerEnv path header headerMessages inputCtx mainModule
  if headerMessages.hasErrors then return .error { parsed := true, messages := headerMessages }
  let mut st : Elab.Frontend.State :=
    { commandState := Elab.Command.mkState env {} opts, parserState, cmdPos := parserState.pos }
  repeat
    let (done, st') ← (Elab.Frontend.processCommand.run { inputCtx }).run st
    st := st'
    if done || stop st.commandState.env then break
  return .ok st.commandState.env

end LeanRefactor.Elaborate
