import RequestProject.AlterPolicy
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

#print axioms PCA.Fix.alter_policy_preserves_roles_and_cmd
#print axioms PCA.Fix.authorized_alter_policy_grant
#print axioms PCA.Fix.authorized_of_extends
#print axioms PCA.Fix.grant_extends

/-!
# Alter Policy Preserves Roles And Cmd
Category: Proof-Carrying Apps
Target: PCA.Fix.alter_policy_preserves_roles_and_cmd
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on file layout: Lean requires `import` commands to be the very first
commands of a file, so this module is deliberately self-contained (it needs
nothing beyond the Lean 4 core library). It is imported by `RequestProject.Main`,
which is built against Mathlib.
-/

namespace PCA

/-- Roles recognised by the isolation engine. -/
inductive Role
  | admin
  | operator
  | reader
  deriving DecidableEq, Repr

/-- Commands an application may attempt to run inside the sandbox. -/
inductive Cmd
  | read
  | write
  | exec
  | net
  deriving DecidableEq, Repr

/-- An isolation policy: which `(role, command)` pairs are permitted. -/
structure Policy where
  allow : Role → Cmd → Bool
  deriving Inhabited

/-- A request presented to the isolation engine: the command to run, the roles
held by the caller, and the policy in force. -/
structure Request where
  cmd : Cmd
  roles : List Role
  policy : Policy

/-- A request is authorized when some role held by the caller is permitted to
run the requested command under the request's policy. -/

theorem alter_policy_id (r : Request) : alterPolicy r id = r := rfl

/-- Successive policy alterations compose. -/
