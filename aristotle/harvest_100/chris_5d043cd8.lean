import Mathlib
import PCA.Fix

/-!
# Alter Policy Preserves Roles And Cmd — Mathlib (`Finset`) variant

Companion to `PCA.Fix`.  The target theorem
`PCA.Fix.alter_policy_preserves_roles_and_cmd` lives in `PCA/Fix.lean`, which
carries the required verbatim header comment and therefore cannot contain an
`import` line (a module docstring must follow, not precede, the imports).

Here the same isolation-engine model is redeveloped over Mathlib's `Finset`
role sets, and the corresponding preservation statement is proved, so that the
result is available in the Mathlib-flavoured setting as well.  A `Finset` model
is transported to the `List` model of `PCA.Fix` by
`PCA.Fix.FinsetModel.toRequest` (faithful when the list enumerates the role
set), and the two preservation theorems agree
(`PCA.Fix.FinsetModel.alterPolicy_toRequest`).
-/

set_option autoImplicit false

namespace PCA
namespace Fix
namespace FinsetModel

/-- A policy over `Finset` role sets: a role-monotone permission predicate. -/
structure Policy where
  /-- `permits roles c` holds when a principal owning `roles` may run `c`. -/
  permits : Finset Role → Cmd → Prop
  /-- Gaining roles never removes a permission. -/
  mono : ∀ {r s : Finset Role} {c : Cmd}, r ⊆ s → permits r c → permits s c

/-- A request whose caller roles form a `Finset`. -/
structure Request where
  /-- The roles held by the caller. -/
  roles : Finset Role
  /-- The command being requested. -/
  cmd : Cmd
  /-- The policy currently in force. -/
  policy : Policy

/-- The engine's verdict on a `Finset`-based request. -/
def Request.authorized (q : Request) : Prop :=
  q.policy.permits q.roles q.cmd

/-- Install a new policy, leaving roles and command untouched. -/
def alterPolicy (q : Request) (p : Policy) : Request :=
  { q with policy := p }

/-- Altering the policy preserves the caller's roles and the requested
command, in the `Finset` model. -/
theorem alter_policy_preserves_roles_and_cmd (q : Request) (p : Policy) :
    (alterPolicy q p).roles = q.roles ∧ (alterPolicy q p).cmd = q.cmd :=
  ⟨rfl, rfl⟩

/-- Authorization after a policy change is the new policy at the original
roles and command. -/
theorem authorized_alterPolicy (q : Request) (p : Policy) :
    (alterPolicy q p).authorized ↔ p.permits q.roles q.cmd := Iff.rfl

/-- A `Finset` policy induces a `List` policy: a role list is permitted when
the finite set of roles it enumerates is. -/
def Policy.toPolicy (p : Policy) : PCA.Fix.Policy where
  permits l c := p.permits l.toFinset c
  mono {r s c} h hp := by
    refine p.mono ?_ hp
    intro a ha
    simp only [List.mem_toFinset] at ha ⊢
    exact h ha

/-- Transport of a `Finset`-based request to the `List`-based model of
`PCA.Fix`. -/
def toRequest (q : Request) (l : List Role) : PCA.Fix.Request where
  roles := l
  cmd := q.cmd
  policy := q.policy.toPolicy

/-- The transport is compatible with the two verdicts. -/
theorem authorized_toRequest (q : Request) (l : List Role)
    (hl : l.toFinset = q.roles) :
    (toRequest q l).authorized ↔ q.authorized := by
  simp only [PCA.Fix.Request.authorized, Request.authorized, toRequest,
    Policy.toPolicy, hl]

/-- The transport intertwines the two `alterPolicy` operations. -/
theorem alterPolicy_toRequest (q : Request) (p : Policy) (l : List Role) :
    toRequest (alterPolicy q p) l
      = PCA.Fix.alterPolicy (toRequest q l) p.toPolicy := rfl

end FinsetModel
end Fix
end PCA

/-!
# Alter Policy Preserves Roles And Cmd
Category: Proof-Carrying Apps
Target: PCA.Fix.alter_policy_preserves_roles_and_cmd
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace PCA
namespace Fix

/-- A role name in the isolation engine's model. -/
abbrev Role := String

/-- A command name that an application may attempt to execute. -/
abbrev Cmd := String

/-- A policy of the isolation engine: it decides, for the roles held by the
caller and a command, whether that command is permitted. -/
structure Policy where
  /-- `permits roles c` holds when a principal owning `roles` may run `c`. -/
  permits : List Role → Cmd → Prop
  /-- Policies are monotone in the roles held: gaining roles never removes a
  permission. -/
  mono : ∀ {r s : List Role} {c : Cmd}, r ⊆ s → permits r c → permits s c

/-- A request submitted to the isolation engine: the roles held by the caller,
the command requested, and the policy in force. -/
structure Request where
  /-- The roles held by the caller. -/
  roles : List Role
  /-- The command being requested. -/
  cmd : Cmd
  /-- The policy currently in force. -/
  policy : Policy

/-- The engine authorizes a request exactly when the policy in force permits
the requested command for the caller's roles. -/
def Request.authorized (q : Request) : Prop :=
  q.policy.permits q.roles q.cmd

/-- `alterPolicy` installs a new policy in a request, leaving the caller's
roles and the requested command untouched. -/
def alterPolicy (q : Request) (p : Policy) : Request :=
  { q with policy := p }

/-- **Target.** Altering the policy of a request preserves both the caller's
roles and the requested command. -/
theorem alter_policy_preserves_roles_and_cmd (q : Request) (p : Policy) :
    (alterPolicy q p).roles = q.roles ∧ (alterPolicy q p).cmd = q.cmd :=
  ⟨rfl, rfl⟩

/-- The altered request carries exactly the policy that was installed. -/
theorem alter_policy_policy (q : Request) (p : Policy) :
    (alterPolicy q p).policy = p := rfl

/-- Installing the policy already in force is a no-op. -/
theorem alter_policy_self (q : Request) : alterPolicy q q.policy = q := rfl

/-- Only the last installed policy matters. -/
theorem alter_policy_idem (q : Request) (p p' : Policy) :
    alterPolicy (alterPolicy q p) p' = alterPolicy q p' := rfl

/-- Authorization after a policy change is the new policy applied to the
*original* roles and command. -/
theorem authorized_alter_policy (q : Request) (p : Policy) :
    (alterPolicy q p).authorized ↔ p.permits q.roles q.cmd := Iff.rfl

/-- Requests agreeing on roles, command and policy are equal: a policy change
is the only difference `alterPolicy` can introduce. -/
theorem request_ext {q q' : Request} (hr : q.roles = q'.roles)
    (hc : q.cmd = q'.cmd) (hp : q.policy = q'.policy) : q = q' := by
  cases q; cases q'; subst hr; subst hc; subst hp; rfl

/-- Monotonicity of the model survives a policy change: enlarging the caller's
roles never revokes authorization. -/
theorem authorized_mono_roles (q : Request) (s : List Role)
    (hs : q.roles ⊆ s) (h : q.authorized) :
    ({ q with roles := s } : Request).authorized :=
  q.policy.mono hs h

end Fix
end PCA

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

