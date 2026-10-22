import Brockian.D5Research
import Lean.Util.CollectAxioms

/-!
Check every theorem in every local Brockian module imported by the focused
D5 target. Imported Mathlib facts are followed transitively by Lean's axiom
collector. The only permitted axioms are Lean's standard extensionality,
choice, and quotient axioms. A project axiom, `sorryAx`, or native decision
oracle makes this command fail.

Run after `lake build Brockian.D5Research`:
`lake env lean -DautoImplicit=false scripts/d5_axiom_audit.lean`.
-/

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut checked : Nat := 0
  let mut modules : Array Name := #[]
  for (name, info) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let moduleName := env.header.moduleNames[idx.toNat]!
      if (`Brockian).isPrefixOf moduleName then
        if !modules.contains moduleName then
          modules := modules.push moduleName
        match info with
        | .axiomInfo _ => throwError "Project axiom found: {name} in {moduleName}"
        | _ => pure ()
        if info.isTheorem then
          let axioms ← collectAxioms name
          let unexpected := axioms.filter (fun ax => !allowed.contains ax)
          if !unexpected.isEmpty then
            throwError "Unexpected axiom dependencies for {name}: {unexpected}"
          checked := checked + 1
          logInfo m!"D5_AXIOMS {name}: {axioms}"
  if checked == 0 then
    throwError "No D5 theorem declarations were audited"
  logInfo m!"D5_AXIOM_AUDIT_PASS theorems={checked} modules={modules.size} allowed={allowed}"
