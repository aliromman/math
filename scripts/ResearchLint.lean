import Lean.Elab.Command

open Lean Elab Command

/-- Check a terminal command before the parser stops reading the file. -/
initialize addLinter {
  run := fun command => do
    if command.isOfKind ``Parser.Command.exit then
      logErrorAt command "The verifier must read the complete research module."
}

/-- Read the full command syntax after message guards have handled their diagnostics. -/
initialize addModuleLinter {
  run := fun commands => do
    for command in commands do
      if let some stx := command.find? (·.isOfKind ``Parser.Command.«example») then
        logErrorAt stx "Give the example a theorem name so the kernel can replay it."
      if let some stx := command.find? (fun s =>
          s.isOfKind ``Parser.Command.«unsafe» || s.isOfKind ``Parser.Command.«partial») then
        logErrorAt stx "The kernel replay skips unsafe and partial declarations."
      if let some stx := command.find? (fun s =>
          [``Parser.Term.«sorry», ``Parser.Tactic.tacticSorry, ``Parser.Tactic.tacticAdmit,
           ``Parser.Tactic.Grind.«sorry», ``Parser.Tactic.Grind.grindAdmit].contains s.getKind) then
        logErrorAt stx "Replace the proof placeholder with a proof."
}
