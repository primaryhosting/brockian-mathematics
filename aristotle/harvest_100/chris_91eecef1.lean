/-!
# Alter Policy Preserves Roles And Cmd
Category: Proof-Carrying Apps
Target: PCA.Fix.alter_policy_preserves_roles_and_cmd
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace PCA

/-- A role held by a principal in the isolation engine's model. -/
abbrev Role := String

/-- A command that a proof-carrying app may attempt to run. -/
abbrev Cmd := String

/-- A policy of the isolation engine: which `(cmd, role)` pairs are permitted. -/
structure Policy where
  /-- `allowed c r` says the policy lets role `r` execute command `c`. -/
  allowed : Cmd → Role → Bool

/-- A capability request handled by the isolation engine: a command, the roles
carried by the requesting principal, and the policy in force. -/
structure Capability where
  /-- The command being requested. -/
  cmd : Cmd
  /-- The roles carried by the requesting principal. -/
  roles : List Role
  /-- The policy currently in force. -/
  policy : Policy

/-- The engine's decision procedure: the request is granted iff some carried
role is permitted to run the command by the policy in force. -/
def Capability.granted (c : Capability) : Bool :=
  c.roles.any fun r => c.policy.allowed c.cmd r

namespace Fix

/-- The "alter policy" repair action of the isolation engine: swap in a new
policy, leaving the request's command and roles untouched. -/
def alterPolicy (c : Capability) (p : Policy) : Capability :=
  { c with policy := p }

/-- **Target.** Altering the policy in force preserves both the roles carried by
the request and the command being requested, while installing exactly the
supplied policy.

Concerning the hint to look for an existing Mathlib lemma: none is needed here.
Structure eta makes each projection of `{ c with policy := p }` definitionally
equal to the corresponding projection of `c` (resp. to `p`), so the goal is
closed by `rfl` on each conjunct (`exact?` likewise reports `⟨rfl, rfl, rfl⟩`,
i.e. `And.intro` applied to `rfl`). -/
theorem alter_policy_preserves_roles_and_cmd (c : Capability) (p : Policy) :
    (alterPolicy c p).roles = c.roles ∧
      (alterPolicy c p).cmd = c.cmd ∧
      (alterPolicy c p).policy = p :=
  ⟨rfl, rfl, rfl⟩

/-- Consequence for the engine's decision procedure: after altering the policy,
the grant decision is obtained by evaluating the *new* policy against the
*unchanged* command and roles. -/
theorem granted_alterPolicy (c : Capability) (p : Policy) :
    (alterPolicy c p).granted = c.roles.any fun r => p.allowed c.cmd r := by
  obtain ⟨hroles, hcmd, hpolicy⟩ := alter_policy_preserves_roles_and_cmd c p
  simp only [Capability.granted, hroles, hcmd, hpolicy]

/-- Altering the policy twice is the same as altering it once with the second
policy. -/
theorem alterPolicy_alterPolicy (c : Capability) (p q : Policy) :
    alterPolicy (alterPolicy c p) q = alterPolicy c q := rfl

/-- Re-installing the policy already in force is a no-op. -/
theorem alterPolicy_self (c : Capability) : alterPolicy c c.policy = c := rfl

end Fix

end PCA

import Mathlib
import RequestProject.PCAFix

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

