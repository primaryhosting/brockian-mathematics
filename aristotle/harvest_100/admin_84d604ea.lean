/-!
# Member Check Prevents Cross Tenant Write
Category: Proof-Carrying Apps
Target: PCA.WriteIntegrity.member_check_prevents_cross_tenant_write
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace PCA
namespace WriteIntegrity

/-! ## The isolation engine's model

We model a multi-tenant write path.  A static environment records which
principals are members of which tenants, and which tenant owns each resource.
The engine's only guard before performing a write is a *member check*: the
actor must be a member of the tenant that owns the targeted resource.

The main theorem says this single check is enough to guarantee tenant
isolation for writes: along an arbitrary trace of write requests, if no actor
appearing in the trace is a member of tenant `t`, then every resource owned by
`t` retains its original value. -/

/-- Tenant identifiers. -/
abbrev TenantId := Nat
/-- Principal (user) identifiers. -/
abbrev UserId := Nat
/-- Resource identifiers. -/
abbrev ResourceId := Nat
/-- Stored values. -/
abbrev Value := Nat

/-- Static environment: tenant membership of principals, tenant ownership of
resources. -/
structure Env where
  /-- `member u t` holds when principal `u` is a member of tenant `t`. -/
  member : UserId → TenantId → Bool
  /-- `owner r` is the tenant that owns resource `r`. -/
  owner : ResourceId → TenantId

/-- Mutable state of the store. -/
structure State where
  /-- Current value of each resource. -/
  store : ResourceId → Value

/-- A write request: a principal asks to set a resource to a value. -/
structure WriteReq where
  /-- The principal issuing the request. -/
  actor : UserId
  /-- The resource being written. -/
  target : ResourceId
  /-- The value to be written. -/
  val : Value

/-- Declarative access-control policy: a write of `r` by `u` is permitted
exactly when `u` is a member of the tenant owning `r`. -/
def MayWrite (E : Env) (u : UserId) (r : ResourceId) : Prop :=
  E.member u (E.owner r) = true

/-- The engine's runtime guard (the *member check*). -/
def guard (E : Env) (q : WriteReq) : Bool :=
  E.member q.actor (E.owner q.target)

/-- One step of the engine: perform the write iff the guard accepts. -/
def step (E : Env) (s : State) (q : WriteReq) : State :=
  if guard E q then
    { store := fun r => if r = q.target then q.val else s.store r }
  else
    s

/-- Execute a trace of write requests. -/
def run (E : Env) (s : State) : List WriteReq → State
  | [] => s
  | q :: qs => run E (step E s q) qs

/-! ## Soundness and completeness of the guard -/

/-- The guard is sound and complete for the declarative policy. -/
theorem guard_iff_mayWrite (E : Env) (q : WriteReq) :
    guard E q = true ↔ MayWrite E q.actor q.target := Iff.rfl

/-- No over-blocking: an authorized write does take effect. -/
theorem step_store_target_of_guard (E : Env) (s : State) (q : WriteReq)
    (h : guard E q = true) : (step E s q).store q.target = q.val := by
  simp [step, h]

/-- A step never touches resources other than its target. -/
theorem step_store_of_ne (E : Env) (s : State) (q : WriteReq) {r : ResourceId}
    (h : r ≠ q.target) : (step E s q).store r = s.store r := by
  unfold step
  by_cases hg : guard E q <;> simp [hg, h]

/-! ## Key intermediate lemma -/

/-- **Key lemma.** A single step by a principal that is not a member of tenant
`t` cannot modify any resource owned by `t`. -/
theorem step_preserves_of_not_member (E : Env) (s : State) (q : WriteReq)
    {t : TenantId} (hq : E.member q.actor t = false)
    {r : ResourceId} (hr : E.owner r = t) :
    (step E s q).store r = s.store r := by
  by_cases h : r = q.target
  · subst h
    have hg : guard E q = false := by
      unfold guard
      rw [hr]
      exact hq
    simp [step, hg]
  · exact step_store_of_ne E s q h

/-! ## Main theorem -/

/-- **Member check prevents cross-tenant writes.**  If no actor occurring in a
trace of write requests is a member of tenant `t`, then after running the whole
trace every resource owned by `t` still holds its initial value. -/
theorem member_check_prevents_cross_tenant_write
    (E : Env) (s : State) (tr : List WriteReq) {t : TenantId}
    (hout : ∀ q ∈ tr, E.member q.actor t = false)
    {r : ResourceId} (hr : E.owner r = t) :
    (run E s tr).store r = s.store r := by
  induction tr generalizing s with
  | nil => rfl
  | cons q qs ih =>
      have hq : E.member q.actor t = false := hout q (List.mem_cons_self ..)
      have hrest : ∀ p ∈ qs, E.member p.actor t = false :=
        fun p hp => hout p (List.mem_cons_of_mem _ hp)
      have h1 : (run E (step E s q) qs).store r = (step E s q).store r :=
        ih hrest (s := step E s q)
      rw [run, h1, step_preserves_of_not_member E s q hq hr]

/-! ## Converse: every observed change is witnessed by an authorized member -/

/-- Soundness of the engine's effects: if the value of `r` changed along the
trace, then some request in the trace targeted `r` and its actor passed the
member check for the tenant owning `r`. -/
theorem change_implies_member (E : Env) (s : State) (tr : List WriteReq)
    {r : ResourceId} (h : (run E s tr).store r ≠ s.store r) :
    ∃ q ∈ tr, q.target = r ∧ MayWrite E q.actor r := by
  induction tr generalizing s with
  | nil => exact absurd rfl h
  | cons q qs ih =>
      rw [run] at h
      by_cases hstep : (step E s q).store r = s.store r
      · have h' : (run E (step E s q) qs).store r ≠ (step E s q).store r := by
          rw [hstep]; exact h
        obtain ⟨p, hp, hp1, hp2⟩ := ih (s := step E s q) h'
        exact ⟨p, List.mem_cons_of_mem _ hp, hp1, hp2⟩
      · have htgt : r = q.target := by
          by_cases hne : r = q.target
          · exact hne
          · exact absurd (step_store_of_ne E s q hne) hstep
        have hg : guard E q = true := by
          by_cases hg : guard E q
          · exact hg
          · exact absurd (by simp [step, hg]) hstep
        refine ⟨q, List.mem_cons_self .., htgt.symm, ?_⟩
        show E.member q.actor (E.owner r) = true
        rw [htgt]
        exact hg

/-- Contrapositive packaging of the main theorem: a cross-tenant actor can
never be the cause of a change to another tenant's resource. -/
theorem no_cross_tenant_effect
    (E : Env) (tr : List WriteReq) {t : TenantId}
    (hout : ∀ q ∈ tr, E.member q.actor t = false)
    {r : ResourceId} (hr : E.owner r = t) :
    ¬ ∃ q ∈ tr, q.target = r ∧ MayWrite E q.actor r := by
  rintro ⟨q, hq, -, hmem⟩
  have : E.member q.actor t = false := hout q hq
  rw [MayWrite, hr, this] at hmem
  exact Bool.noConfusion hmem

/-! ## Sanity checks: the model is not vacuous

In `demoEnv` each principal `u` is a member of exactly the tenant `u`, and every
resource is owned by tenant `0`.  A write by principal `0` (a member) takes
effect, while the same write attempted by principal `1` (a cross-tenant actor)
is blocked. -/

/-- Example environment used for the sanity checks below. -/
def demoEnv : Env := { member := fun u t => u == t, owner := fun _ => 0 }

/-- Example initial state used for the sanity checks below. -/
def demoState : State := { store := fun _ => 0 }

example : (step demoEnv demoState ⟨0, 5, 7⟩).store 5 = 7 := rfl

example : (step demoEnv demoState ⟨1, 5, 7⟩).store 5 = 0 := rfl

end WriteIntegrity
end PCA

import RequestProject.PCA
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

