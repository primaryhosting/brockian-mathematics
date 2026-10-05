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

theorem alter_policy_comp (f g : Policy → Policy) (c : Config) :
    (alterPolicy g (alterPolicy f c)).roles = c.roles ∧
      (alterPolicy g (alterPolicy f c)).cmd = c.cmd ∧
      (alterPolicy g (alterPolicy f c)).policy = g (f c.policy) :=
  ⟨rfl, rfl, rfl⟩

/-- The audit log only ever grows under an alteration: the previous log is a suffix. -/
