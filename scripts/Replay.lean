import LeanChecker

/-- Run the release's exact-module checker in a fresh process for each source. -/
private unsafe def checkModule : IO Unit := do
  let some target ← IO.getEnv "RESEARCH_REPLAY_MODULE"
    | throw <| IO.userError "missing research module"
  Lean.initSearchPath (← Lean.findSysroot)
  replayFromImports target.toName

#eval checkModule
