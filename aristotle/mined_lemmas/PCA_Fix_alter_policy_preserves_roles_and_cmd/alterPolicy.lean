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

def alterPolicy (f : Policy → Policy) (c : Config) : Config :=
  let p' := f c.policy
  { roles := c.roles
    cmd := c.cmd
    policy := p'
    log := (if c.roles.any (fun r => p'.grants r c.cmd) then "allow" else "deny") :: c.log }

/-- **Main result.** Altering the policy preserves both the roles held by the
principal and the command under consideration. -/
