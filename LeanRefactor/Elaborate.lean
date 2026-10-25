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

/-- Build the environment `header` imports, set up as `lean` sets it up under lake: the module's
    `dynlibs` loaded and its `plugins` handed to the import, so an imported `initialize` that calls
    an `@[extern]` finds the native symbol (without them: "Could not find native implementation of
    external declaration"), and the module's options in force. -/
public def headerEnv (path : String) (header : Elab.HeaderSyntax) (messages : MessageLog)
    (inputCtx : Parser.InputContext) (mainModule : Name) : IO (Environment × MessageLog × Options) := do
  let setup ← setupOf path mainModule
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

end LeanRefactor.Elaborate
