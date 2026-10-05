/-!
# Member Check Prevents Cross Tenant Write
Category: Proof-Carrying Apps
Target: PCA.WriteIntegrity.member_check_prevents_cross_tenant_write
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace PCA.WriteIntegrity

/-- Tenant identifiers. -/
abbrev Tenant := Nat
/-- Principal (user / service account) identifiers. -/
abbrev Principal := Nat
/-- Resource identifiers. -/
abbrev ResourceId := Nat
/-- Values stored in resources. -/
abbrev Value := Nat

/-- The isolation policy of the engine: which principals are members of which
tenant, and which tenant owns which resource. -/
structure Policy where
  /-- `member p t` holds when principal `p` is a member of tenant `t`. -/
  member : Principal → Tenant → Bool
  /-- `owner i` is the tenant owning resource `i`. -/
  owner : ResourceId → Tenant

/-- A write request: an actor asking to set a resource to a value. -/
structure WriteReq where
  /-- The principal issuing the request. -/
  actor : Principal
  /-- The resource to be written. -/
  target : ResourceId
  /-- The value to be written. -/
  value : Value

/-- The state of the store: a value for every resource. -/
abbrev Store := ResourceId → Value

/-- Point update of the store. -/
def Store.write (s : Store) (i : ResourceId) (v : Value) : Store :=
  fun j => if j = i then v else s j

@[simp] theorem Store.write_self (s : Store) (i : ResourceId) (v : Value) :
    s.write i v i = v := by
  simp [Store.write]

theorem Store.write_of_ne (s : Store) {i j : ResourceId} (v : Value) (h : j ≠ i) :
    s.write i v j = s j := by
  simp [Store.write, h]

/-- The member check performed by the engine before every write: the actor must
be a member of the tenant owning the target resource. -/
def authorized (P : Policy) (r : WriteReq) : Bool :=
  P.member r.actor (P.owner r.target)

/-- One step of the engine: a write is applied only if the member check passes;
otherwise the store is unchanged. -/
def step (P : Policy) (s : Store) (r : WriteReq) : Store :=
  if authorized P r then s.write r.target r.value else s

/-- Running a whole trace of write requests through the engine. -/
def run (P : Policy) (s : Store) : List WriteReq → Store
  | [] => s
  | r :: rs => run P (step P s r) rs

@[simp] theorem run_nil (P : Policy) (s : Store) : run P s [] = s := rfl

@[simp] theorem run_cons (P : Policy) (s : Store) (r : WriteReq) (rs : List WriteReq) :
    run P s (r :: rs) = run P (step P s r) rs := rfl

/-- A rejected request leaves the store completely untouched. -/
theorem step_of_not_authorized (P : Policy) (s : Store) (r : WriteReq)
    (h : ¬ authorized P r) : step P s r = s := by
  simp [step, h]

/-- An accepted request writes exactly its value at its target. -/
theorem step_target_of_authorized (P : Policy) (s : Store) (r : WriteReq)
    (h : authorized P r) : step P s r r.target = r.value := by
  simp [step, h]

/-- A single step cannot change a resource whose owning tenant does not contain
the requesting actor. -/
theorem step_eq_of_not_member (P : Policy) (s : Store) (r : WriteReq) (i : ResourceId)
    (h : ¬ P.member r.actor (P.owner i)) : step P s r i = s i := by
  by_cases ha : authorized P r
  · have hne : i ≠ r.target := by
      intro hEq
      exact h (hEq ▸ ha)
    simp [step, ha, Store.write_of_ne _ _ hne]
  · simp [step, ha]

/-- Any change made by a single step at resource `i` must come from an
authorized request targeting `i`. -/
theorem step_ne_imp (P : Policy) (s : Store) (r : WriteReq) (i : ResourceId)
    (h : step P s r i ≠ s i) : r.target = i ∧ authorized P r := by
  by_cases ha : authorized P r
  · refine ⟨?_, ha⟩
    by_cases hEq : i = r.target
    · exact hEq.symm
    · exact absurd (by simp [step, ha, Store.write_of_ne _ _ hEq]) h
  · exact absurd (by simp [step, ha]) h

/-- **Main theorem (cross-tenant write prevention).**
If every request in a trace is issued by a principal that is *not* a member of
the tenant owning resource `i`, then the engine's final store agrees with the
initial store at `i`: no cross-tenant write can occur. -/
theorem member_check_prevents_cross_tenant_write
    (P : Policy) (s : Store) (trace : List WriteReq) (i : ResourceId)
    (h : ∀ r ∈ trace, ¬ P.member r.actor (P.owner i)) :
    run P s trace i = s i := by
  induction trace generalizing s with
  | nil => rfl
  | cons r rs ih =>
      have hr : ¬ P.member r.actor (P.owner i) := h r (by simp)
      have hrest : ∀ q ∈ rs, ¬ P.member q.actor (P.owner i) :=
        fun q hq => h q (by simp [hq])
      rw [run_cons, ih (step P s r) hrest, step_eq_of_not_member P s r i hr]

/-- Corollary: a single outsider principal `a`, issuing an arbitrary trace of
write requests, cannot modify any resource of a tenant it does not belong to. -/
theorem outsider_cannot_write
    (P : Policy) (s : Store) (trace : List WriteReq) (a : Principal) (i : ResourceId)
    (hactor : ∀ r ∈ trace, r.actor = a)
    (hout : ¬ P.member a (P.owner i)) :
    run P s trace i = s i :=
  member_check_prevents_cross_tenant_write P s trace i
    (fun r hr => by rw [hactor r hr]; exact hout)

/-- Attribution: if the store changed at `i` over a trace, then some request in
the trace targeted `i`, passed the member check, and its actor really is a
member of the tenant owning `i`. -/
theorem exists_authorized_writer_of_changed
    (P : Policy) (s : Store) (trace : List WriteReq) (i : ResourceId)
    (h : run P s trace i ≠ s i) :
    ∃ r ∈ trace, r.target = i ∧ authorized P r ∧ P.member r.actor (P.owner i) := by
  induction trace generalizing s with
  | nil => exact absurd rfl h
  | cons r rs ih =>
      by_cases hstep : step P s r i = s i
      · obtain ⟨q, hq, hq1, hq2, hq3⟩ := ih (step P s r) (by rw [hstep]; exact h)
        exact ⟨q, List.mem_cons_of_mem _ hq, hq1, hq2, hq3⟩
      · obtain ⟨htgt, hauth⟩ := step_ne_imp P s r i hstep
        refine ⟨r, by simp, htgt, hauth, ?_⟩
        rw [authorized, htgt] at hauth
        exact hauth

/-- Completeness of the engine: a legitimate in-tenant write does take effect. -/
theorem member_write_succeeds
    (P : Policy) (s : Store) (r : WriteReq)
    (h : P.member r.actor (P.owner r.target)) :
    step P s r r.target = r.value :=
  step_target_of_authorized P s r h

/-! ## A concrete instance

A two-tenant example checked by `decide`, confirming the model is not vacuous:
principal `0` belongs to tenant `0`, principal `1` to tenant `1`; resource `0`
is owned by tenant `0` and resource `1` by tenant `1`. -/

/-- Example policy: principal `p` is a member of tenant `t` iff `p = t`. -/
def demoPolicy : Policy where
  member p t := p == t
  owner i := i

/-- Example initial store: every resource holds `0`. -/
def demoStore : Store := fun _ => 0

/-- Principal `1` attempting to write `7` into resource `0` (owned by tenant `0`)
is rejected: the store is unchanged. -/
example : run demoPolicy demoStore [⟨1, 0, 7⟩] 0 = 0 := by decide

/-- Principal `0` writing `7` into its own tenant's resource `0` succeeds. -/
example : run demoPolicy demoStore [⟨0, 0, 7⟩] 0 = 7 := by decide

/-- Even a long trace of outsider writes leaves resource `0` untouched. -/
example : run demoPolicy demoStore [⟨1, 0, 7⟩, ⟨2, 0, 8⟩, ⟨1, 1, 9⟩] 0 = 0 := by decide

end PCA.WriteIntegrity

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

