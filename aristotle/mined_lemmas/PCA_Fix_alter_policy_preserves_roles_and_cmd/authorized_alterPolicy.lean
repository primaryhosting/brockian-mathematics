/-!
# Alter Policy Preserves Roles And Cmd
Category: Proof-Carrying Apps
Target: PCA.Fix.alter_policy_preserves_roles_and_cmd
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace PCA.Fix

/-- A role name granted to a principal by the isolation engine. -/
abbrev Role := String

/-- A command that a principal may attempt to run. -/
abbrev Cmd := String

/-- A policy of the isolation engine: which role may run which command. -/
structure Policy where
  grants : Role → Cmd → Bool

/-- A configuration of the isolation engine: the roles held by the current
principal, the command under consideration, the active policy, and an audit log. -/
structure Config where
  roles : List Role
  cmd : Cmd
  policy : Policy
  log : List String

/-- The command of a configuration is authorized when some held role grants it. -/

theorem authorized_alterPolicy (f : Policy → Policy) (c : Config) :
    (alterPolicy f c).authorized = c.roles.any (fun r => (f c.policy).grants r c.cmd) := rfl

/-- Altering by the identity leaves roles, command and policy unchanged
(only the audit log grows). -/
