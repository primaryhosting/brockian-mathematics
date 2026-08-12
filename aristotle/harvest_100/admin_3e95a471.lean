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
# A formal model of a multi-tenant write-isolation engine

This file develops a small but complete operational model of the write path of a
multi-tenant isolation engine ("PCA"), together with soundness and completeness
theorems for its membership check.

* `PCA.WriteIntegrity.Config` is the (static) isolation configuration: which tenant owns
  each resource, and which principals are members of which tenant.
* `PCA.WriteIntegrity.authorize` is the executable membership check performed by the engine
  on each write request.
* `PCA.WriteIntegrity.step` / `PCA.WriteIntegrity.run` are the operational semantics: a write
  request mutates the store exactly when the check succeeds, and is a no-op otherwise.

The main results are

* `PCA.WriteIntegrity.authorize_iff` : the executable check is *sound and complete*
  with respect to the declarative membership specification;
* `PCA.WriteIntegrity.member_check_prevents_cross_tenant_write` : along any trace of
  requests, if the contents of a resource change then some request in the trace targeted
  that resource and was issued by a principal that is a member of the tenant owning it —
  i.e. no cross-tenant write can ever take effect;
* `PCA.WriteIntegrity.run_eq_of_no_member_request` : the contrapositive form (traces made
  entirely of cross-tenant requests are observationally inert);
* `PCA.WriteIntegrity.authorized_write_effective` : the engine does not over-block, an
  in-tenant write does take effect.
-/

namespace PCA
namespace WriteIntegrity

/-- Tenant identifiers. -/
abbrev Tenant := Nat
/-- Principal (user / service account) identifiers. -/
abbrev Principal := Nat
/-- Resource (object) identifiers. -/
abbrev Resource := Nat
/-- Values stored in resources. -/
abbrev Value := Nat

/-- The static isolation configuration: every resource belongs to exactly one tenant,
and membership of principals in tenants is decided by an executable predicate. -/
structure Config where
  /-- The tenant owning a given resource. -/
  owner : Resource → Tenant
  /-- The engine's membership table. -/
  memberOf : Principal → Tenant → Bool

/-- Declarative reading of the membership table. -/
def Config.Member (c : Config) (p : Principal) (t : Tenant) : Prop :=
  c.memberOf p t = true

/-- A write request. -/
structure Request where
  /-- The principal issuing the request. -/
  principal : Principal
  /-- The targeted resource. -/
  resource : Resource
  /-- The value to be written. -/
  value : Value

/-- A request is *cross-tenant* when its issuer is not a member of the tenant owning the
targeted resource. -/
def CrossTenant (c : Config) (q : Request) : Prop :=
  ¬ c.Member q.principal (c.owner q.resource)

/-- The store: current contents of every resource. -/
abbrev Store := Resource → Value

/-- The engine's membership check on a write request. -/
def authorize (c : Config) (q : Request) : Bool :=
  c.memberOf q.principal (c.owner q.resource)

/-- Operational semantics of a single request: the write is applied exactly when the
membership check succeeds; otherwise the store is unchanged. -/
def step (c : Config) (s : Store) (q : Request) : Store :=
  if authorize c q then Function.update s q.resource q.value else s

/-- Operational semantics of a trace of requests. -/
def run (c : Config) (s : Store) : List Request → Store
  | [] => s
  | q :: qs => run c (step c s q) qs

@[simp] theorem run_nil (c : Config) (s : Store) : run c s [] = s := rfl

@[simp] theorem run_cons (c : Config) (s : Store) (q : Request) (qs : List Request) :
    run c s (q :: qs) = run c (step c s q) qs := rfl

/-! ### Soundness and completeness of the membership check -/

/-- **Soundness and completeness** of the engine's check: it accepts a request exactly
when the issuing principal really is a member of the tenant owning the target. -/
theorem authorize_iff (c : Config) (q : Request) :
    authorize c q = true ↔ c.Member q.principal (c.owner q.resource) := Iff.rfl

/-- Soundness: an accepted request is in-tenant. -/
theorem authorize_sound (c : Config) (q : Request) (h : authorize c q = true) :
    c.Member q.principal (c.owner q.resource) := h

/-- Completeness: an in-tenant request is accepted. -/
theorem authorize_complete (c : Config) (q : Request)
    (h : c.Member q.principal (c.owner q.resource)) : authorize c q = true := h

/-- A cross-tenant request is rejected. -/
theorem authorize_eq_false_of_crossTenant (c : Config) (q : Request) (h : CrossTenant c q) :
    authorize c q = false := by
  simpa [CrossTenant, Config.Member, authorize, Bool.not_eq_true] using h

/-! ### Single-step properties -/

/-- A rejected (cross-tenant) request is a complete no-op. -/
theorem step_eq_of_crossTenant (c : Config) (s : Store) (q : Request) (h : CrossTenant c q) :
    step c s q = s := by
  simp [step, authorize_eq_false_of_crossTenant c q h]

/-- A step never modifies a resource other than the one targeted. -/
theorem step_apply_of_ne (c : Config) (s : Store) (q : Request) (r : Resource)
    (h : q.resource ≠ r) : step c s q r = s r := by
  unfold step
  split
  · exact Function.update_of_ne (Ne.symm h) _ _
  · rfl

/-- If a step changes the contents of `r`, the request targeted `r` and was in-tenant. -/
theorem targeted_and_member_of_step_ne (c : Config) (s : Store) (q : Request) (r : Resource)
    (h : step c s q r ≠ s r) :
    q.resource = r ∧ c.Member q.principal (c.owner r) := by
  by_cases hr : q.resource = r
  · subst hr
    refine ⟨rfl, ?_⟩
    by_contra hm
    exact h (by rw [step_eq_of_crossTenant c s q hm])
  · exact absurd (step_apply_of_ne c s q r hr) h

/-- The engine does not over-block: an in-tenant write does take effect. -/
theorem authorized_write_effective (c : Config) (s : Store) (q : Request)
    (h : c.Member q.principal (c.owner q.resource)) :
    step c s q q.resource = q.value := by
  simp [step, authorize_complete c q h]

/-! ### Trace-level integrity -/

/-- **Main theorem (write integrity).** If, after running an arbitrary trace of write
requests, the contents of resource `r` differ from their initial value, then the trace
must contain a request that targeted `r` and whose issuing principal is a member of the
tenant owning `r`. Consequently no cross-tenant write can ever affect the store. -/
theorem member_check_prevents_cross_tenant_write
    (c : Config) (s : Store) (qs : List Request) (r : Resource)
    (h : run c s qs r ≠ s r) :
    ∃ q ∈ qs, q.resource = r ∧ c.Member q.principal (c.owner r) := by
  induction qs generalizing s with
  | nil => exact absurd rfl h
  | cons q qs ih =>
      rw [run_cons] at h
      by_cases hstep : step c s q r = s r
      · obtain ⟨q', hq', hq'2⟩ := ih (s := step c s q) (by rw [hstep]; exact h)
        exact ⟨q', List.mem_cons_of_mem _ hq', hq'2⟩
      · exact ⟨q, List.mem_cons_self, targeted_and_member_of_step_ne c s q r hstep⟩

/-- Contrapositive form: if every request in the trace that targets `r` is cross-tenant,
then the contents of `r` are untouched. -/
theorem run_eq_of_no_member_request
    (c : Config) (s : Store) (qs : List Request) (r : Resource)
    (h : ∀ q ∈ qs, q.resource = r → ¬ c.Member q.principal (c.owner r)) :
    run c s qs r = s r := by
  by_contra hne
  obtain ⟨q, hq, hqr, hmem⟩ := member_check_prevents_cross_tenant_write c s qs r hne
  exact h q hq hqr hmem

/-- A trace consisting entirely of cross-tenant requests leaves the store completely
unchanged. -/
theorem run_eq_of_all_crossTenant
    (c : Config) (s : Store) (qs : List Request) (h : ∀ q ∈ qs, CrossTenant c q) :
    run c s qs = s := by
  induction qs generalizing s with
  | nil => rfl
  | cons q qs ih =>
      rw [run_cons, step_eq_of_crossTenant c s q (h q List.mem_cons_self)]
      exact ih s fun q' hq' => h q' (List.mem_cons_of_mem _ hq')

end WriteIntegrity
end PCA

