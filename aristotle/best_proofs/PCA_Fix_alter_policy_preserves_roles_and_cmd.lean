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

/-!
# A formal model of a policy-controlled isolation engine

This file develops a small but complete formal model of the *isolation engine* of a
privileged-command arbiter (`PCA`).  A request carries

* the set of `roles` held by the caller,
* the `cmd` (privileged command) that is being requested,
* the `policy` currently in force,

and the engine returns a boolean decision.  The engine is *deny-overrides*: a request is
executed when some held role is granted the command and no held role is denied it.

We prove:

* `PCA.Engine.decision_sound`  — the boolean engine only accepts requests that the
  declarative semantics `PCA.Permits` allows;
* `PCA.Engine.decision_complete` — the boolean engine accepts every request that the
  declarative semantics allows (so `PCA.Engine.decision_iff_permits` is an exact
  characterisation, i.e. the engine model is sound *and* complete);
* `PCA.Engine.isolation` — the decision only depends on the fragment of the policy that
  mentions the requested command: policies that agree on `cmd` are indistinguishable
  (command isolation / non-interference);
* the `PCA.Fix` layer: repairing a request by altering the policy, with
  `PCA.Fix.alter_policy_preserves_roles_and_cmd` as the key frame property, and
  `PCA.Fix.repair_permits` showing the repair really does make the request executable.
-/

namespace PCA

/-- A role identifier. -/
abbrev Role : Type := Nat

/-- A privileged command identifier. -/
abbrev Cmd : Type := Nat

/-- A policy is a pair of access-control lists: explicit grants and explicit denials,
each recorded as a `(role, command)` pair. -/
structure Policy where
  allow : List (Role × Cmd)
  deny : List (Role × Cmd)
  deriving DecidableEq, Repr

/-- A request presented to the isolation engine. -/
structure Request where
  roles : List Role
  cmd : Cmd
  policy : Policy
  deriving DecidableEq, Repr

namespace Policy

/-- `p.allows r c` holds when the policy explicitly grants command `c` to role `r`. -/
def allows (p : Policy) (r : Role) (c : Cmd) : Bool := decide ((r, c) ∈ p.allow)

/-- `p.denies r c` holds when the policy explicitly denies command `c` to role `r`. -/
def denies (p : Policy) (r : Role) (c : Cmd) : Bool := decide ((r, c) ∈ p.deny)

@[simp] theorem allows_iff (p : Policy) (r : Role) (c : Cmd) :
    p.allows r c = true ↔ (r, c) ∈ p.allow := by
  simp [allows]

@[simp] theorem denies_iff (p : Policy) (r : Role) (c : Cmd) :
    p.denies r c = true ↔ (r, c) ∈ p.deny := by
  simp [denies]

/-- Add an explicit grant of `c` to `r`. -/
def grant (p : Policy) (r : Role) (c : Cmd) : Policy :=
  { p with allow := (r, c) :: p.allow }

/-- Remove every denial of the command `c`. -/
def clearDenials (p : Policy) (c : Cmd) : Policy :=
  { p with deny := p.deny.filter (fun q => decide (q.2 ≠ c)) }

@[simp] theorem mem_clearDenials (p : Policy) (c : Cmd) (q : Role × Cmd) :
    q ∈ (p.clearDenials c).deny ↔ q ∈ p.deny ∧ q.2 ≠ c := by
  simp [clearDenials, List.mem_filter]

@[simp] theorem mem_grant_allow (p : Policy) (r : Role) (c : Cmd) (q : Role × Cmd) :
    q ∈ (p.grant r c).allow ↔ q = (r, c) ∨ q ∈ p.allow := by
  simp [grant]

@[simp] theorem grant_deny (p : Policy) (r : Role) (c : Cmd) :
    (p.grant r c).deny = p.deny := rfl

@[simp] theorem clearDenials_allow (p : Policy) (c : Cmd) :
    (p.clearDenials c).allow = p.allow := rfl

end Policy

/-- Declarative semantics of the engine: the policy `p` permits the command `c` to a
caller holding the roles `rs` exactly when some held role is granted `c` and no held role
is denied `c` (deny overrides allow). -/
def Permits (p : Policy) (rs : List Role) (c : Cmd) : Prop :=
  (∃ r ∈ rs, (r, c) ∈ p.allow) ∧ ∀ r ∈ rs, (r, c) ∉ p.deny

namespace Engine

/-- The executable decision procedure of the isolation engine. -/
def decision (q : Request) : Bool :=
  q.roles.any (fun r => q.policy.allows r q.cmd) &&
    !q.roles.any (fun r => q.policy.denies r q.cmd)

/-- **Soundness**: whatever the engine accepts is permitted by the declarative semantics. -/
theorem decision_sound (q : Request) (h : decision q = true) :
    Permits q.policy q.roles q.cmd := by
  simp only [decision, Bool.and_eq_true, Bool.not_eq_true', List.any_eq_true,
    List.any_eq_false, Policy.allows_iff, Policy.denies_iff] at h
  obtain ⟨⟨r, hr, hra⟩, hd⟩ := h
  refine ⟨⟨r, hr, hra⟩, fun r' hr' hmem => ?_⟩
  have := hd r' hr'
  simp [hmem] at this

/-- **Completeness**: whatever the declarative semantics permits is accepted by the engine. -/
theorem decision_complete (q : Request) (h : Permits q.policy q.roles q.cmd) :
    decision q = true := by
  obtain ⟨⟨r, hr, hra⟩, hd⟩ := h
  simp only [decision, Bool.and_eq_true, Bool.not_eq_true', List.any_eq_true,
    List.any_eq_false, Policy.allows_iff, Policy.denies_iff]
  refine ⟨⟨r, hr, hra⟩, fun r' hr' => ?_⟩
  simp [hd r' hr']

/-- The engine model is exactly the declarative semantics. -/
theorem decision_iff_permits (q : Request) :
    decision q = true ↔ Permits q.policy q.roles q.cmd :=
  ⟨decision_sound q, decision_complete q⟩

/-- **Command isolation** (non-interference): the decision on a request depends only on
the fragment of the policy that mentions the requested command.  Changing grants and
denials of *other* commands cannot change the decision. -/
theorem isolation (rs : List Role) (c : Cmd) (p₁ p₂ : Policy)
    (ha : ∀ r : Role, ((r, c) ∈ p₁.allow ↔ (r, c) ∈ p₂.allow))
    (hd : ∀ r : Role, ((r, c) ∈ p₁.deny ↔ (r, c) ∈ p₂.deny)) :
    decision ⟨rs, c, p₁⟩ = decision ⟨rs, c, p₂⟩ := by
  have key : ∀ p : Policy, decision ⟨rs, c, p⟩ = true ↔
      ((∃ r ∈ rs, (r, c) ∈ p.allow) ∧ ∀ r ∈ rs, (r, c) ∉ p.deny) :=
    fun p => decision_iff_permits ⟨rs, c, p⟩
  have : (decision ⟨rs, c, p₁⟩ = true) ↔ (decision ⟨rs, c, p₂⟩ = true) := by
    rw [key, key]
    constructor
    · rintro ⟨⟨r, hr, hra⟩, hdn⟩
      exact ⟨⟨r, hr, (ha r).1 hra⟩, fun r' hr' hmem => hdn r' hr' ((hd r').2 hmem)⟩
    · rintro ⟨⟨r, hr, hra⟩, hdn⟩
      exact ⟨⟨r, hr, (ha r).2 hra⟩, fun r' hr' hmem => hdn r' hr' ((hd r').1 hmem)⟩
  cases h₁ : decision ⟨rs, c, p₁⟩ <;> cases h₂ : decision ⟨rs, c, p₂⟩ <;>
    simp [h₁, h₂] at this ⊢

end Engine

namespace Fix

/-- The primitive repair action of the isolation engine: install a new policy, leaving
the caller's roles and the requested command untouched. -/
def alter_policy (q : Request) (p : Policy) : Request :=
  { q with policy := p }

/-- **Frame property of the repair layer.**  Altering the policy of a request changes
neither the caller's roles nor the requested command. -/
theorem alter_policy_preserves_roles_and_cmd (q : Request) (p : Policy) :
    (alter_policy q p).roles = q.roles ∧ (alter_policy q p).cmd = q.cmd := by
  exact ⟨rfl, rfl⟩

@[simp] theorem alter_policy_policy (q : Request) (p : Policy) :
    (alter_policy q p).policy = p := rfl

@[simp] theorem alter_policy_roles (q : Request) (p : Policy) :
    (alter_policy q p).roles = q.roles := rfl

@[simp] theorem alter_policy_cmd (q : Request) (p : Policy) :
    (alter_policy q p).cmd = q.cmd := rfl

/-- Altering the policy twice is the same as altering it once. -/
@[simp] theorem alter_policy_idem (q : Request) (p₁ p₂ : Policy) :
    alter_policy (alter_policy q p₁) p₂ = alter_policy q p₂ := rfl

/-- Reinstalling the current policy is a no-op. -/
@[simp] theorem alter_policy_self (q : Request) : alter_policy q q.policy = q := rfl

/-- The repair of a request for a role `r`: grant the command to `r` and drop every
denial of that command. -/
def repair (q : Request) (r : Role) : Request :=
  alter_policy q ((q.policy.clearDenials q.cmd).grant r q.cmd)

/-- Repairing a request preserves the caller's roles and the requested command. -/
theorem repair_preserves_roles_and_cmd (q : Request) (r : Role) :
    (repair q r).roles = q.roles ∧ (repair q r).cmd = q.cmd :=
  alter_policy_preserves_roles_and_cmd q _

/-- **Adequacy of the repair.**  If `r` is one of the caller's roles, the repaired
request is permitted by the declarative semantics. -/
theorem repair_permits (q : Request) (r : Role) (hr : r ∈ q.roles) :
    Permits (repair q r).policy (repair q r).roles (repair q r).cmd := by
  refine ⟨⟨r, hr, ?_⟩, fun r' _ hmem => ?_⟩
  · simp [repair]
  · simp only [repair, alter_policy_policy, alter_policy_cmd, Policy.grant_deny,
      Policy.mem_clearDenials] at hmem
    exact hmem.2 rfl

/-- The engine accepts every repaired request (for a role actually held by the caller). -/
theorem decision_repair (q : Request) (r : Role) (hr : r ∈ q.roles) :
    Engine.decision (repair q r) = true :=
  Engine.decision_complete _ (repair_permits q r hr)

end Fix

end PCA

