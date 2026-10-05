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

def Config.authorized (c : Config) : Bool :=
  c.roles.any (fun r => c.policy.grants r c.cmd)

/-- Altering the policy: the engine installs the new policy and appends a fresh
audit entry recording the new decision, leaving roles and command untouched. -/

def alterPolicy (f : Policy → Policy) (c : Config) : Config :=
  let p' := f c.policy
  { roles := c.roles
    cmd := c.cmd
    policy := p'
    log := (if c.roles.any (fun r => p'.grants r c.cmd) then "allow" else "deny") :: c.log }

/-- **Main result.** Altering the policy preserves both the roles held by the
principal and the command under consideration. -/

theorem alter_policy_preserves_roles_and_cmd (f : Policy → Policy) (c : Config) :
    (alterPolicy f c).roles = c.roles ∧ (alterPolicy f c).cmd = c.cmd :=
  ⟨rfl, rfl⟩

/-- The altered configuration carries exactly the new policy. -/
