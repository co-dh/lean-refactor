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

/-- `lake setup-file path`, the setup Lake hands the editor for a file no target builds: its last
    line of output is the `ModuleSetup`. Nothing when Lake cannot give one. -/
def setupOf (path : String) : IO ModuleSetup := do
  let none : ModuleSetup := { name := .anonymous }
  try
    let out ← IO.Process.output { cmd := "lake", args := #["setup-file", path] }
    if out.exitCode != 0 then return none
    let some line := (out.stdout.splitOn "\n").reverse.find? (·.startsWith "{") | return none
    match Json.parse line >>= fromJson? with
    | .ok setup => return setup
    | .error _ => return none
  catch _ => return none

/-- Parse `source`'s import header, build the environment its imports define, and run the frontend
    over the rest.  Stops there: what a COMMAND error means is the caller's decision, not this one's.
    The environment handed back is the one the IMPORTS built, which is what re-elaborating an edit
    of the same file needs; `frontend.commandState.env` is the one the commands left behind. -/
public def frontendOf (path source : String) (mainModule : Name) :
    IO (Except HeaderError (Parser.InputContext × Environment × Elab.Frontend.State)) := do
  let inputCtx := Parser.mkInputContext source path
  let (header, parserState, headerMessages) ← Parser.parseHeader inputCtx
  if headerMessages.hasErrors then return .error { parsed := false, messages := headerMessages }
  -- The native code Lake hands `lean` for this module, which `lean` loads from the same file: a
  -- target built with `precompileModules` runs its own `@[extern]` kernels while elaborating
  -- (`#eval`, `#guard`), and without its dynlibs and plugins the interpreter aborts the whole tool
  -- on the first such symbol. A file no target builds has no setup file of its own; Lake answers
  -- one for it as it does for the editor, and a file it cannot answer for loads nothing.
  let setupPath := modToFilePath ".lake/build/ir" mainModule "setup.json"
  let setup ← if ← setupPath.pathExists then ModuleSetup.load setupPath else setupOf path
  -- the toolchain's own libraries (Lake's, for a lakefile) are already this process's: loaded again
  -- they register their environment extensions twice
  let sysroot := (← findSysroot).toString
  let theirs (l : System.FilePath) := !l.toString.startsWith sysroot
  (setup.dynlibs.filter theirs).forM loadDynlib
  let (env, headerMessages) ← Elab.processHeader header {} headerMessages inputCtx
    (plugins := setup.plugins.filter theirs) (mainModule := mainModule)
  if headerMessages.hasErrors then return .error { parsed := true, messages := headerMessages }
  let frontend ← Elab.IO.processCommands inputCtx parserState (Elab.Command.mkState env {} {})
  return .ok (inputCtx, env, frontend)

end LeanRefactor.Elaborate
