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
set_option relaxedAutoImplicit false

namespace PCA
namespace WriteIntegrity

universe u v w x

/-- A stored row: the tenant that owns it together with its payload. -/
structure Row (Tenant : Type v) (Val : Type x) where
  tenant : Tenant
  value : Val
  deriving DecidableEq

/-- A store maps keys to (optional) owned rows. -/
def Store (Tenant : Type v) (Key : Type w) (Val : Type x) : Type (max v w x) :=
  Key → Option (Row Tenant Val)

/-- A write request issued by a principal, acting on behalf of `tenant`. -/
structure WriteReq (Principal : Type u) (Tenant : Type v) (Key : Type w) (Val : Type x) where
  principal : Principal
  tenant : Tenant
  key : Key
  value : Val

/-- The membership oracle: `mem p t = true` iff principal `p` is a member of tenant `t`. -/
abbrev MemberCheck (Principal : Type u) (Tenant : Type v) : Type (max u v) :=
  Principal → Tenant → Bool

variable {Principal : Type u} {Tenant : Type v} {Key : Type w} {Val : Type x}

section
variable [DecidableEq Tenant] [DecidableEq Key]

/-- Ownership check: the targeted key is either free, or already owned by the
acting tenant. -/
def ownerOk (st : Store Tenant Key Val) (r : WriteReq Principal Tenant Key Val) : Bool :=
  match st r.key with
  | none => true
  | some row => decide (row.tenant = r.tenant)

/-- The isolation engine's guard: the member check together with the ownership check. -/
def allowed (mem : MemberCheck Principal Tenant) (st : Store Tenant Key Val)
    (r : WriteReq Principal Tenant Key Val) : Bool :=
  mem r.principal r.tenant && ownerOk st r

/-- The guarded write: the store is updated only if the guard accepts the request. -/
def applyWrite (mem : MemberCheck Principal Tenant) (st : Store Tenant Key Val)
    (r : WriteReq Principal Tenant Key Val) : Store Tenant Key Val :=
  fun k =>
    if allowed mem st r then
      (if k = r.key then some ⟨r.tenant, r.value⟩ else st k)
    else st k

/-! ## Soundness of the guard -/

/-- **Main theorem (isolation / soundness).**
A guarded write never disturbs a row owned by a tenant of which the acting principal is
not a member: cross-tenant writes are impossible. -/
theorem member_check_prevents_cross_tenant_write
    (mem : MemberCheck Principal Tenant) (st : Store Tenant Key Val)
    (r : WriteReq Principal Tenant Key Val) (k : Key) (row : Row Tenant Val)
    (hrow : st k = some row) (hmem : mem r.principal row.tenant = false) :
    applyWrite mem st r k = st k := by
  unfold applyWrite
  by_cases hk : k = r.key
  · subst hk
    have hno : allowed mem st r = false := by
      unfold allowed ownerOk
      cases hown : mem r.principal r.tenant with
      | false => simp
      | true =>
        have hne : row.tenant ≠ r.tenant := by
          intro h
          rw [h, hown] at hmem
          exact Bool.noConfusion hmem
        simp [hrow, hne]
    simp [hno]
  · simp [hk]

/-- A denied request leaves the whole store untouched. -/
theorem denied_write_is_noop (mem : MemberCheck Principal Tenant) (st : Store Tenant Key Val)
    (r : WriteReq Principal Tenant Key Val) (h : allowed mem st r = false) :
    applyWrite mem st r = st := by
  funext k; simp [applyWrite, h]

/-- Locality: a write only ever affects the key it targets. -/
theorem write_affects_only_target_key (mem : MemberCheck Principal Tenant)
    (st : Store Tenant Key Val) (r : WriteReq Principal Tenant Key Val) (k : Key)
    (hk : k ≠ r.key) : applyWrite mem st r k = st k := by
  simp [applyWrite, hk]

/-- Every actual state change is attributable to an authorized, ownership-respecting write. -/
theorem change_implies_authorized (mem : MemberCheck Principal Tenant)
    (st : Store Tenant Key Val) (r : WriteReq Principal Tenant Key Val) (k : Key)
    (hne : applyWrite mem st r k ≠ st k) :
    k = r.key ∧ mem r.principal r.tenant = true ∧ ownerOk st r = true ∧
      applyWrite mem st r k = some ⟨r.tenant, r.value⟩ := by
  by_cases hk : k = r.key
  · subst hk
    cases hal : allowed mem st r with
    | false =>
      exact absurd (congrFun (denied_write_is_noop mem st r hal) r.key) hne
    | true =>
      have h : mem r.principal r.tenant = true ∧ ownerOk st r = true := by
        have h' : allowed mem st r = true := hal
        unfold allowed at h'
        exact Bool.and_eq_true .. |>.mp h'
      exact ⟨rfl, h.1, h.2, by simp [applyWrite, hal]⟩
  · exact absurd (write_affects_only_target_key mem st r k hk) hne

/-- The post-state of a key is always the pre-state, or a row freshly owned by the
acting tenant, of which the principal is a member. -/
theorem post_state_owner (mem : MemberCheck Principal Tenant) (st : Store Tenant Key Val)
    (r : WriteReq Principal Tenant Key Val) (k : Key) (row : Row Tenant Val)
    (h : applyWrite mem st r k = some row) :
    st k = some row ∨ (row.tenant = r.tenant ∧ mem r.principal r.tenant = true) := by
  cases hal : allowed mem st r with
  | false =>
    exact Or.inl (by rw [← h, congrFun (denied_write_is_noop mem st r hal) k])
  | true =>
    by_cases hk : k = r.key
    · subst hk
      have hm : mem r.principal r.tenant = true := by
        have h' : allowed mem st r = true := hal
        unfold allowed at h'
        exact (Bool.and_eq_true .. |>.mp h').1
      simp only [applyWrite, hal, if_true, Option.some.injEq] at h
      exact Or.inr ⟨congrArg Row.tenant h.symm, hm⟩
    · exact Or.inl (by rw [← h, write_affects_only_target_key mem st r k hk])

/-! ## Completeness of the guard -/

/-- **Completeness.** If the principal is a member of the acting tenant and the ownership
check passes, then the write really is committed. -/
theorem authorized_write_commits (mem : MemberCheck Principal Tenant)
    (st : Store Tenant Key Val) (r : WriteReq Principal Tenant Key Val)
    (hmem : mem r.principal r.tenant = true) (hown : ownerOk st r = true) :
    applyWrite mem st r r.key = some ⟨r.tenant, r.value⟩ := by
  have hal : allowed mem st r = true := by simp [allowed, hmem, hown]
  simp [applyWrite, hal]

omit [DecidableEq Key] in
/-- The guard accepts exactly the requests from members that respect existing ownership. -/
theorem allowed_iff (mem : MemberCheck Principal Tenant) (st : Store Tenant Key Val)
    (r : WriteReq Principal Tenant Key Val) :
    allowed mem st r = true ↔
      (mem r.principal r.tenant = true ∧ ∀ row, st r.key = some row → row.tenant = r.tenant) := by
  unfold allowed ownerOk
  rw [Bool.and_eq_true]
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    intro row hrow
    have h2 := h.2
    rw [hrow] at h2
    exact of_decide_eq_true h2
  · intro h
    refine ⟨h.1, ?_⟩
    cases hst : st r.key with
    | none => rfl
    | some row => exact decide_eq_true (h.2 row hst)

end

/-! ## Sanity check: the model is non-trivial

Two tenants `0` and `1`; principal `0` is a member of tenant `0` only. Tenant `1` owns
key `0`. Principal `0`'s attempt to overwrite it is rejected, while its write to the free
key `1` commits. -/

section Example

/-- Membership: principal `p` is a member of tenant `p` only. -/
def demoMem : MemberCheck Nat Nat := fun p t => decide (p = t)

/-- Key `0` is owned by tenant `1`; every other key is free. -/
def demoStore : Store Nat Nat Nat := fun k => if k = 0 then some ⟨1, 7⟩ else none

/-- Principal `0` (member of tenant `0` only) tries to overwrite tenant `1`'s row. -/
def crossTenantReq : WriteReq Nat Nat Nat Nat := ⟨0, 0, 0, 99⟩

/-- Principal `0` writes, as tenant `0`, to the free key `1`. -/
def ownTenantReq : WriteReq Nat Nat Nat Nat := ⟨0, 0, 1, 99⟩

example : applyWrite demoMem demoStore crossTenantReq 0 = some ⟨1, 7⟩ := by
  decide

example : applyWrite demoMem demoStore ownTenantReq 1 = some ⟨0, 99⟩ := by
  decide

end Example

end WriteIntegrity
end PCA

