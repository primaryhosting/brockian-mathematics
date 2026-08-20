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

theorem granted_alterPolicy (c : Capability) (p : Policy) :
    (alterPolicy c p).granted = c.roles.any fun r => p.allowed c.cmd r := by
  obtain ⟨hroles, hcmd, hpolicy⟩ := alter_policy_preserves_roles_and_cmd c p
  simp only [Capability.granted, hroles, hcmd, hpolicy]

/-- Altering the policy twice is the same as altering it once with the second
policy. -/
