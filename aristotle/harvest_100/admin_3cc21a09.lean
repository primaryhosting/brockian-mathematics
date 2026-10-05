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
# Member Check Prevents Cross Tenant Write
Category: Proof-Carrying Apps
Target: PCA.WriteIntegrity.member_check_prevents_cross_tenant_write
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace PCA
namespace WriteIntegrity

universe u v w x

variable {Tenant : Type u} {User : Type v} {Res : Type w} {Val : Type x}

/-- A store maps each resource to its current value. -/
abbrev Store (Res : Type w) (Val : Type x) : Type (max w x) := Res → Val

/-- Pointwise update of a store. -/
def upd [DecidableEq Res] (st : Store Res Val) (r : Res) (v : Val) : Store Res Val :=
  fun r' => if r' = r then v else st r'

@[simp] theorem upd_self [DecidableEq Res] (st : Store Res Val) (r : Res) (v : Val) :
    upd st r v r = v := by
  simp [upd]

@[simp] theorem upd_of_ne [DecidableEq Res] (st : Store Res Val) {r r' : Res} (v : Val)
    (h : r' ≠ r) : upd st r v r' = st r' := by
  simp [upd, h]

/-- The isolation policy of the engine: every resource belongs to exactly one tenant,
and a membership check decides whether a user acts on behalf of a tenant. -/
structure Policy (Tenant : Type u) (User : Type v) (Res : Type w) where
  /-- The (unique) tenant owning a resource. -/
  tenantOf : Res → Tenant
  /-- The membership check: `member u t = true` iff user `u` is a member of tenant `t`. -/
  member : User → Tenant → Bool

/-- A write request: an actor writes a value to a target resource. -/
structure Request (User : Type v) (Res : Type w) (Val : Type x) where
  /-- The user issuing the write. -/
  actor : User
  /-- The resource being written. -/
  target : Res
  /-- The value to be written. -/
  value : Val

/-- The guard installed by the engine: a write is admitted only if the actor is a
member of the tenant owning the target resource. -/
def authorized (pol : Policy Tenant User Res) (req : Request User Res Val) : Bool :=
  pol.member req.actor (pol.tenantOf req.target)

/-- One step of the write-integrity engine: the request is applied only if the
member check succeeds; otherwise the store is left untouched. -/
def step [DecidableEq Res] (pol : Policy Tenant User Res)
    (req : Request User Res Val) (st : Store Res Val) : Store Res Val :=
  if authorized pol req then upd st req.target req.value else st

/-- Running a whole trace of requests through the engine. -/
def run [DecidableEq Res] (pol : Policy Tenant User Res)
    (trace : List (Request User Res Val)) (st : Store Res Val) : Store Res Val :=
  trace.foldl (fun s r => step pol r s) st

@[simp] theorem run_nil [DecidableEq Res] (pol : Policy Tenant User Res)
    (st : Store Res Val) : run pol [] st = st := rfl

@[simp] theorem run_cons [DecidableEq Res] (pol : Policy Tenant User Res)
    (req : Request User Res Val) (trace : List (Request User Res Val))
    (st : Store Res Val) :
    run pol (req :: trace) st = run pol trace (step pol req st) := rfl

/-- A rejected request has no effect at all. -/
theorem step_of_not_authorized [DecidableEq Res] {pol : Policy Tenant User Res}
    {req : Request User Res Val} (st : Store Res Val)
    (h : authorized pol req = false) : step pol req st = st := by
  simp [step, h]

/-- An admitted request writes exactly its value at exactly its target. -/
theorem step_of_authorized [DecidableEq Res] {pol : Policy Tenant User Res}
    {req : Request User Res Val} (st : Store Res Val)
    (h : authorized pol req = true) :
    step pol req st = upd st req.target req.value := by
  simp [step, h]

/-- Contrapositive core lemma: if a single step actually changes the value stored at
some resource `res`, then `res` is the target of the request and the actor passed the
member check for the tenant owning `res`. -/
theorem member_of_step_ne [DecidableEq Res] {pol : Policy Tenant User Res}
    {req : Request User Res Val} {st : Store Res Val} {res : Res}
    (h : step pol req st res ≠ st res) :
    res = req.target ∧ pol.member req.actor (pol.tenantOf res) = true := by
  cases hauth : authorized pol req with
  | false =>
      exact absurd (congrFun (step_of_not_authorized st hauth) res) h
  | true =>
      rw [step_of_authorized st hauth] at h
      by_cases hres : res = req.target
      · subst hres
        exact ⟨rfl, hauth⟩
      · exact absurd (upd_of_ne st _ hres) h

/-- **Single-step isolation.** If the actor of a request fails the member check for the
tenant owning a resource `res`, then the engine leaves `res` untouched: the member check
prevents any cross-tenant write. -/
theorem step_eq_of_not_member [DecidableEq Res] {pol : Policy Tenant User Res}
    {req : Request User Res Val} (st : Store Res Val) {res : Res}
    (h : pol.member req.actor (pol.tenantOf res) = false) :
    step pol req st res = st res := by
  cases hauth : authorized pol req with
  | false => exact congrFun (step_of_not_authorized st hauth) res
  | true =>
      rw [step_of_authorized st hauth]
      have hres : res ≠ req.target := by
        intro hEq
        subst hEq
        rw [authorized, h] at hauth
        exact Bool.noConfusion hauth
      exact upd_of_ne st _ hres

/-- **Main theorem (write integrity / tenant isolation).**

Consider a trace of write requests processed by the engine, and a resource `res`.
If *no* actor occurring in the trace passes the member check for the tenant that owns
`res`, then the value stored at `res` is unchanged by the whole trace.

In other words, the member check performed by the guard is sufficient to rule out every
cross-tenant write: a user can only ever affect resources belonging to tenants it is a
member of. -/
theorem member_check_prevents_cross_tenant_write [DecidableEq Res]
    (pol : Policy Tenant User Res) (trace : List (Request User Res Val))
    (st : Store Res Val) (res : Res)
    (h : ∀ req ∈ trace, pol.member req.actor (pol.tenantOf res) = false) :
    run pol trace st res = st res := by
  induction trace generalizing st with
  | nil => rfl
  | cons req rest ih =>
      rw [run_cons, ih (step pol req st) (fun r hr => h r (List.mem_cons_of_mem _ hr))]
      exact step_eq_of_not_member st (h req (by simp))

/-- Equivalent contrapositive form of the main theorem: whenever the engine does change
the stored value of a resource `res`, some request in the trace was issued by an actor
that passed the member check for the tenant owning `res`. -/
theorem exists_member_of_run_ne [DecidableEq Res]
    (pol : Policy Tenant User Res) (trace : List (Request User Res Val))
    (st : Store Res Val) (res : Res)
    (h : run pol trace st res ≠ st res) :
    ∃ req ∈ trace, pol.member req.actor (pol.tenantOf res) = true := by
  refine Classical.byContradiction (fun hcon => h ?_)
  refine member_check_prevents_cross_tenant_write pol trace st res (fun req hreq => ?_)
  cases hm : pol.member req.actor (pol.tenantOf res) with
  | false => rfl
  | true => exact absurd ⟨req, hreq, hm⟩ hcon

/-- **Completeness of the guard (no over-blocking).** A request issued by a genuine
member of the tenant owning the target does take effect. -/
theorem step_apply_of_member [DecidableEq Res] (pol : Policy Tenant User Res)
    (req : Request User Res Val) (st : Store Res Val)
    (h : pol.member req.actor (pol.tenantOf req.target) = true) :
    step pol req st req.target = req.value := by
  rw [step_of_authorized st h]
  exact upd_self st _ _

end WriteIntegrity
end PCA

