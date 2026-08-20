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
def Authorized (r : Request) : Prop :=
  ∃ role ∈ r.roles, r.policy.allow role r.cmd = true

/-- One policy extends another when it permits at least as much. -/
def Extends (p q : Policy) : Prop :=
  ∀ role c, q.allow role c = true → p.allow role c = true

namespace Fix

/-- The engine's policy-repair step: replace the policy of a request by
`f` applied to it, leaving every other component of the request untouched. -/
def alterPolicy (r : Request) (f : Policy → Policy) : Request :=
  { r with policy := f r.policy }

/-- **Target.** Altering the policy of a request preserves both the roles held
by the caller and the command being requested. -/
theorem alter_policy_preserves_roles_and_cmd (r : Request) (f : Policy → Policy) :
    (alterPolicy r f).roles = r.roles ∧ (alterPolicy r f).cmd = r.cmd :=
  ⟨rfl, rfl⟩

/-- Altering the policy indeed installs the new policy. -/
theorem alter_policy_policy (r : Request) (f : Policy → Policy) :
    (alterPolicy r f).policy = f r.policy :=
  rfl

/-- Altering by the identity is a no-op. -/
theorem alter_policy_id (r : Request) : alterPolicy r id = r := rfl

/-- Successive policy alterations compose. -/
theorem alter_policy_comp (r : Request) (f g : Policy → Policy) :
    alterPolicy (alterPolicy r f) g = alterPolicy r (g ∘ f) :=
  rfl

/-- The repair used by the engine: grant `role` the right to run `c`, keeping
every other decision of the policy unchanged. -/
def grant (role : Role) (c : Cmd) (p : Policy) : Policy :=
  { allow := fun role' c' =>
      p.allow role' c' || (decide (role' = role) && decide (c' = c)) }

/-- Granting only ever adds permissions. -/
theorem grant_extends (role : Role) (c : Cmd) (p : Policy) : Extends (grant role c p) p := by
  intro role' c' h
  simp [grant, h]

/-- Soundness of the repair step: after granting `role` the command `r.cmd`,
the request is authorized provided the caller actually holds `role`. -/
theorem authorized_alter_policy_grant (r : Request) (role : Role) (hrole : role ∈ r.roles) :
    Authorized (alterPolicy r (grant role r.cmd)) := by
  refine ⟨role, hrole, ?_⟩
  simp [alterPolicy, grant]

/-- Monotonicity: authorization is preserved by any policy alteration that only
extends the policy in force. -/
theorem authorized_of_extends (r : Request) (f : Policy → Policy)
    (hf : Extends (f r.policy) r.policy) (h : Authorized r) :
    Authorized (alterPolicy r f) := by
  obtain ⟨role, hmem, hallow⟩ := h
  exact ⟨role, hmem, hf role r.cmd hallow⟩

end Fix

end PCA

