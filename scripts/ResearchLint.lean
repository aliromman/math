import Lean.Elab.Command

open Lean Elab Command

/-- Anonymous examples have no proof body in the module for kernel replay. -/
initialize addLinter {
  run := fun command => do
    if let some stx := command.find? (·.isOfKind ``Parser.Command.«example») then
      logErrorAt stx "Give the example a theorem name so the kernel can replay it."
    if let some stx := command.find? (fun s =>
        s.isOfKind ``Parser.Command.«unsafe» || s.isOfKind ``Parser.Command.«partial») then
      logErrorAt stx "The kernel replay skips unsafe and partial declarations."
    if command.isOfKind ``Parser.Command.exit then
      logErrorAt command "The verifier must read the complete research module."
}
