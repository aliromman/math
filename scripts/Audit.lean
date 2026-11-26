module

import all Lean.Util.CollectAxioms
import Lean

open Lean

/-- Check the private environment. Share the dependency cache across declarations. -/
private def audit (env : Environment) (modules : Array Name) (contract : String) : IO Unit := do
  let mut names : Array Name := #[]
  for (name, info) in env.constants do
    if let some i := env.getModuleIdxFor? name then
      if modules.contains env.header.moduleNames[i.toNat]! then
        if info.isUnsafe || info.isPartial then
          throw <| IO.userError s!"kernel replay skips {name}"
        names := names.push name
  let footprints := CollectAxioms.runM env do
    names.mapM (CollectAxioms.collectAndGet (fun _ _ => none))
  let mut localAxioms : Std.HashMap Name (Array Name) := {}
  for name in names, axs in footprints do
    for ax in axs do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throw <| IO.userError s!"{name} depends on forbidden axiom {ax}"
    localAxioms := localAxioms.insert name axs
  let mut seen : NameSet := {}
  for line in contract.splitOn "\n" do
    let fields := line.splitOn " " |>.filter (!·.isEmpty)
    if fields.isEmpty then continue
    let statement := fields.head? == some "statement"
    let name :: expected := (if statement then fields.drop 1 else fields)
      | throw <| IO.userError "missing declaration name"
    let name := name.toName
    let some actual := localAxioms[name]?
      | throw <| IO.userError s!"missing local declaration {name}"
    let some info := env.find? name | throw <| IO.userError s!"unknown declaration {name}"
    unless (if statement then info.isDefinition && info.type.isProp else info matches .thmInfo _) do
      throw <| IO.userError s!"incorrect declaration kind for {name}"
    if seen.contains name then throw <| IO.userError s!"duplicate expectation for {name}"
    seen := seen.insert name
    unless actual == (expected.map String.toName).toArray.qsort Name.lt do
      throw <| IO.userError s!"{name}: expected {expected}, found {actual}"
  if seen.isEmpty then throw <| IO.userError "empty axiom contract"
  IO.println s!"Checked {names.size} local declarations and {seen.size} exact axiom expectations."

public unsafe def main (args : List String) : IO Unit := do
  let file :: targets := args | throw <| IO.userError "expected an axiom file and module names"
  let modules := targets.toArray.map String.toName
  initSearchPath (← findSysroot)
  withImportModules (modules.map fun m => { module := m, importAll := true }) {} fun env => do
    audit env modules (← IO.FS.readFile file)
