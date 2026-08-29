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

/-!
# Alter Policy Preserves Roles And Cmd
Category: Proof-Carrying Apps
Target: PCA.Fix.alter_policy_preserves_roles_and_cmd
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace PCA.Fix

/-- A role identifier used by the isolation engine. -/
abbrev Role := String

/-- A command identifier used by the isolation engine. -/
abbrev Cmd := String

/-- An access-control policy: for each role and command it records whether the
command is explicitly allowed and whether it is explicitly denied. -/
structure Policy where
  allows : Role → Cmd → Bool
  denies : Role → Cmd → Bool

/-- A task submitted to the isolation engine: the command to run, the roles the
requesting principal holds, and the policy currently in force. -/
structure Task where
  cmd : Cmd
  roles : List Role
  policy : Policy

/-- The engine admits a task when some role of the principal allows the command
and no role of the principal denies it. -/

theorem not_run_of_roles_or_cmd_ne (t u : Task) (es : List Event)
    (h : u.roles ≠ t.roles ∨ u.cmd ≠ t.cmd) : run t es ≠ u := by
  obtain ⟨h₁, h₂⟩ := alter_policy_preserves_roles_and_cmd t es
  rintro rfl
  rcases h with h | h
  · exact h h₁
  · exact h h₂

/-- Non-triviality: policy alteration is not the identity — it really can flip the
engine's admission decision, while (by the main theorem) leaving the roles and the
command untouched. -/
