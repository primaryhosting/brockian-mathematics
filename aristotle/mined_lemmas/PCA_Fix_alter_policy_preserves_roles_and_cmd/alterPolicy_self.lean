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

