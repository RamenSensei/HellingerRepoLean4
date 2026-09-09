import Lean.Replay

/-! Independent kernel replay of every declaration originating in a project
module, including private helpers and generated declarations. The base
imports only non-project dependencies, and an explicit disjointness check
prevents replay from accepting already imported project theorems. -/

open Lean

namespace HellingerReplay

def isProjectModule (name : Name) : Bool := (`Hellinger).isPrefixOf name

def fromProject (env : Environment) (name : Name) : Bool :=
  match env.getModuleIdxFor? name with
  | none => false
  | some idx => isProjectModule env.header.moduleNames[idx.toNat]!

def main : IO Unit := do
  initSearchPath (← findSysroot)
  let source ← importModules #[{ module := `Hellinger }] {} (trustLevel := 0) (loadExts := false)
  let dependencies := source.allImportedModuleNames.filter (fun n => !isProjectModule n)
  let base ← importModules (dependencies.map fun n => { module := n }) {}
    (trustLevel := 0) (loadExts := false)
  if base.allImportedModuleNames.any isProjectModule then
    throw <| IO.userError "REPLAY_REFUSED: a project module is present in the base environment"
  let mut project : Std.HashMap Name ConstantInfo := {}
  let mut theoremCount := 0
  let mut privateCount := 0
  for (name, info) in source.constants.toList do
    if fromProject source name then
      if base.toKernelEnv.find? name |>.isSome then
        throw <| IO.userError s!"REPLAY_REFUSED: project declaration already exists in base: {name}"
      if info.isUnsafe || info.isPartial then
        throw <| IO.userError s!"REPLAY_REFUSED: unsafe or partial project declaration: {name}"
      if info.isAxiom then
        throw <| IO.userError s!"REPLAY_REFUSED: project axiom: {name}"
      if name != info.name then
        throw <| IO.userError s!"REPLAY_REFUSED: noncanonical constant-map entry: {name} / {info.name}"
      project := project.insert name info
      if info.isTheorem then theoremCount := theoremCount + 1
      if isPrivateName name then privateCount := privateCount + 1
  if project.isEmpty || theoremCount == 0 then
    throw <| IO.userError "REPLAY_REFUSED: no project proof declarations were loaded"
  IO.println s!"REPLAY_START declarations={project.size} theorems={theoremCount} private={privateCount} base_project_modules=0"
  -- Environment.replay invokes Kernel.Environment.addDeclCore directly,
  -- with no option-based bypass. It orders dependencies recursively and
  -- compares constructors and recursors against the regenerated ones.
  let checked ← base.replay project
  for (name, _) in project.toList do
    unless checked.toKernelEnv.find? name |>.isSome do
      throw <| IO.userError s!"REPLAY_REFUSED: declaration absent after replay: {name}"
  -- A deliberately ill-typed proof term must fail even though it introduces
  -- no nonstandard axioms. An axiom allowlist alone cannot detect this case.
  let badName := `HellingerReplay.invalidProofControl
  if base.toKernelEnv.find? badName |>.isSome then
    throw <| IO.userError "REPLAY_REFUSED: negative-control name already exists"
  let bad : ConstantInfo := .thmInfo {
    name := badName, levelParams := [], type := mkConst ``False,
    value := mkConst ``True.intro, all := [badName] }
  let rejected ← try
    let _ ← base.replay (({} : Std.HashMap Name ConstantInfo).insert badName bad)
    pure false
  catch ex =>
    let message := ex.toString
    unless message.contains "declaration type mismatch" do
      throw <| IO.userError s!"REPLAY_REFUSED: negative control failed for an unexpected reason: {message}"
    pure true
  unless rejected do
    throw <| IO.userError "REPLAY_REFUSED: the kernel accepted the ill-typed negative control"
  IO.println "REPLAY_NEGATIVE_CONTROL ill_typed_proof=rejected"
  IO.println s!"REPLAY_SUCCESS declarations={project.size} theorems={theoremCount} private={privateCount}"

end HellingerReplay

def main : IO Unit := HellingerReplay.main
