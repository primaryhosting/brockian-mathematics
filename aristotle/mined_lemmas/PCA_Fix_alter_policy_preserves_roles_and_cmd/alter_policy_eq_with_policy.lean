/-!
# Alter Policy Preserves Roles And Cmd
Category: Proof-Carrying Apps
Target: PCA.Fix.alter_policy_preserves_roles_and_cmd
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

universe u

namespace PCA.Fix

/-! ## The isolation engine model

A *proof-carrying app* is described by a manifest consisting of

* a command line (`cmd`),
* a list of granted roles (`roles`),
* an isolation policy (`policy`).

The isolation engine only ever produces *canonical* manifests: empty command
arguments are dropped and the role list is canonicalised (deduplicated and put
into a fixed order of decreasing privilege).  Re-configuring an app by applying
a list of policy edits re-runs the engine's build pipeline, so a priori it could
also change the command line or the roles.  The target theorem states that on
well-formed (i.e. engine-produced) manifests this never happens: altering the
policy preserves roles and command exactly. -/

/-- The roles an app can be granted. -/
inductive Role
  | reader
  | writer
  | admin
  deriving DecidableEq, Repr

/-- All roles, in the engine's canonical order (decreasing privilege). -/

theorem alter_policy_eq_with_policy {m : Manifest} (hm : WF m) (es : List Edit) :
    alterPolicy m es = { m with policy := applyEdits m.policy es } := by
  obtain ⟨hr, hc⟩ := alter_policy_preserves_roles_and_cmd hm es
  cases m
  simp_all [alterPolicy, build]

/-! ## Sanity checks: the hypothesis is satisfiable and genuinely needed -/

/-- A concrete well-formed manifest, so the main theorem is not vacuous. -/
example : WF { cmd := ["app", "--safe"], roles := [Role.admin, Role.reader],
               policy := { allowNet := true, allowFS := false, memLimit := 64,
                           denied := ["exec"] } } :=
  ⟨by decide, by decide⟩

/-- Dropping well-formedness, the command line really can change. -/
example :
    (alterPolicy { cmd := ["", "app"], roles := [], policy :=
        { allowNet := false, allowFS := false, memLimit := 0, denied := [] } } []).cmd
      ≠ ["", "app"] := by decide

/-- Dropping well-formedness, the role list really can change. -/
example :
    (alterPolicy { cmd := [], roles := [Role.reader, Role.admin], policy :=
        { allowNet := false, allowFS := false, memLimit := 0, denied := [] } } []).roles
      ≠ [Role.reader, Role.admin] := by decide

#print axioms PCA.Fix.alter_policy_preserves_roles_and_cmd

end PCA.Fix

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

