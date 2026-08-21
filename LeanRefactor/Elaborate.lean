module

-- `public` because the signature below is spelled in Lean's own types.
public import Lean

open Lean

namespace LeanRefactor.Elaborate

/-- Why a file's import header could not be used.  `parsed` is false when the header did not even
    parse; `messages` is the log UNPRINTED, so each caller keeps its own reporting. -/
public structure HeaderError where
  parsed : Bool
  messages : MessageLog

/-- Parse `source`'s import header, build the environment its imports define, and run the frontend
    over the rest.  Stops there: what a COMMAND error means is the caller's decision, not this one's.
    The environment handed back is the one the IMPORTS built, which is what re-elaborating an edit
    of the same file needs; `frontend.commandState.env` is the one the commands left behind. -/
public def frontendOf (path source : String) (mainModule : Name) :
    IO (Except HeaderError (Parser.InputContext × Environment × Elab.Frontend.State)) := do
  let inputCtx := Parser.mkInputContext source path
  let (header, parserState, headerMessages) ← Parser.parseHeader inputCtx
  if headerMessages.hasErrors then return .error { parsed := false, messages := headerMessages }
  let (env, headerMessages) ← Elab.processHeader header {} headerMessages inputCtx
    (mainModule := mainModule)
  if headerMessages.hasErrors then return .error { parsed := true, messages := headerMessages }
  let frontend ← Elab.IO.processCommands inputCtx parserState (Elab.Command.mkState env {} {})
  return .ok (inputCtx, env, frontend)

end LeanRefactor.Elaborate
