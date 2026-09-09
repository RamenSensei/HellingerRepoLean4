import Hellinger
import Lean.Util.CollectAxioms

/-! Independent dependency audit of every declaration from a project module,
including private helpers and generated declarations. Namespaced local probes
are included so the external negative controls remain effective.
This command is an auditor, not a proof-producing shortcut. -/

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  let entries := env.constants.toList.filter fun (n, _) =>
    (`Hellinger).isPrefixOf n ||
      match env.getModuleIdxFor? n with
      | none => true
      | some idx => (`Hellinger).isPrefixOf env.header.moduleNames[idx.toNat]!
  for (name, info) in entries.toArray.qsort (fun a b => Name.lt a.1 b.1) do
    let axioms ← collectAxioms name
    let forbidden := axioms.filter (fun a => !allowed.contains a)
    unless forbidden.isEmpty do
      throwError "Unapproved axioms in {name}: {forbidden.toList}"
    logInfo m!"AUDIT_DECLARATION {name}"
    declarations := declarations + 1
    if info.isTheorem then
      theorems := theorems + 1
      logInfo m!"AUDIT_THEOREM {name}: {axioms.toList}"
  if theorems == 0 then
    throwError "No project theorems were imported; refusing an empty audit."
  logInfo m!"AUDIT_SUCCESS declarations={declarations} theorems={theorems}"
