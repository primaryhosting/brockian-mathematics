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

namespace PCA.WriteIntegrity

/-! ## The model

A minimal multi-tenant store.  Every stored record carries the identifier of the
tenant that owns it.  A write request is executed by the isolation engine only
after a *member check*: the acting user must be a member of the tenant scope of
the request, and the record targeted by the request must already be owned by
that same tenant.

The theorems below say that this guard is exactly right:

* **soundness** (`member_check_prevents_cross_tenant_write`): no cross-tenant
  write is possible — every location the engine actually modifies holds a record
  whose owning tenant the acting user is a member of, and the owning tenant of
  that record is unchanged by the write;
* **completeness** (`authorized_write_succeeds`, `authorized_characterization`):
  the guard does not over-block — an authorized write does take effect, and the
  guard passes in precisely the intended situations.
-/

/-- User identifiers. -/
abbrev UserId := Nat
/-- Tenant identifiers. -/
abbrev TenantId := Nat
/-- Resource (record) identifiers. -/
abbrev ResId := Nat
/-- Payloads stored in records. -/
abbrev Value := Nat

/-- A stored record: a payload together with the tenant that owns it. -/
structure Record where
  /-- The tenant owning this record. -/
  tenant : TenantId
  /-- The stored payload. -/
  value : Value
deriving DecidableEq, Repr

/-- A store maps resource identifiers to records (`none` = no such record). -/
abbrev Store := ResId → Option Record

/-- Point update of a store. -/
def Store.update (st : Store) (k : ResId) (r : Option Record) : Store :=
  fun x => if x = k then r else st x

@[simp] theorem Store.update_self (st : Store) (k : ResId) (r : Option Record) :
    st.update k r k = r := by
  simp [Store.update]

theorem Store.update_of_ne (st : Store) {k x : ResId} (h : x ≠ k) (r : Option Record) :
    st.update k r x = st x := by
  simp [Store.update, h]

/-- The deployment environment: the tenant membership relation of the app. -/
structure Env where
  /-- `member u t` is `true` when user `u` is a member of tenant `t`. -/
  member : UserId → TenantId → Bool

/-- A write request: user `user`, acting in tenant scope `tenant`, wants to store
`value` at resource `target`. -/
structure Req where
  /-- The acting user. -/
  user : UserId
  /-- The tenant scope claimed by the request. -/
  tenant : TenantId
  /-- The targeted resource. -/
  target : ResId
  /-- The payload to be written. -/
  value : Value

/-- The record currently stored at the target of a request, if any. -/
def targetRecord (st : Store) (q : Req) : Option Record := st q.target

/-- The guard: the acting user must be a member of the claimed tenant, and the
targeted record must exist and be owned by that tenant. -/
def authorized (E : Env) (st : Store) (q : Req) : Bool :=
  E.member q.user q.tenant &&
    (match targetRecord st q with
     | some r => decide (r.tenant = q.tenant)
     | none => false)

/-- One step of the isolation engine: perform the write if and only if the member
check succeeds. -/
def step (E : Env) (st : Store) (q : Req) : Store :=
  if authorized E st q then
    st.update q.target (some { tenant := q.tenant, value := q.value })
  else
    st

/-- A *cross-tenant write* at location `rid`: the engine changed the contents of
`rid`, yet either `rid` held no record at all, or the acting user is not a member
of the tenant that owned it, or the write changed the owning tenant of that
record. -/
def CrossTenantWrite (E : Env) (st : Store) (q : Req) (rid : ResId) : Prop :=
  step E st q rid ≠ st rid ∧
    (∀ r : Record, st rid = some r →
      E.member q.user r.tenant = false ∨
        ∀ r' : Record, step E st q rid = some r' → r'.tenant ≠ r.tenant)

/-! ## Basic facts about the guard -/

/-- If the guard passes, the target record exists and is owned by the claimed
tenant, of which the acting user is a member. -/
theorem of_authorized (E : Env) (st : Store) (q : Req) (h : authorized E st q = true) :
    E.member q.user q.tenant = true ∧ ∃ v : Value, st q.target = some ⟨q.tenant, v⟩ := by
  rw [authorized, Bool.and_eq_true] at h
  obtain ⟨hm, hr⟩ := h
  refine ⟨hm, ?_⟩
  unfold targetRecord at hr
  cases hst : st q.target with
  | none => rw [hst] at hr; simp at hr
  | some r =>
    rw [hst] at hr
    simp only [decide_eq_true_eq] at hr
    exact ⟨r.value, by cases r; simp_all⟩

/-- The engine never changes a location other than the request's target. -/
theorem step_eq_of_ne (E : Env) (st : Store) (q : Req) {rid : ResId} (h : rid ≠ q.target) :
    step E st q rid = st rid := by
  unfold step
  split
  · exact Store.update_of_ne st h _
  · rfl

/-- If the guard fails, the store is untouched. -/
theorem step_eq_of_unauthorized (E : Env) (st : Store) (q : Req)
    (h : authorized E st q = false) : step E st q = st := by
  unfold step
  rw [h]
  rfl

/-! ## Soundness -/

/-- Explicit ("positive") form of the soundness statement: any location the
engine modifies held a record owned by a tenant the acting user belongs to, and
the write preserves that owning tenant. -/
theorem modified_location_is_own_tenant
    (E : Env) (st : Store) (q : Req) (rid : ResId) (hne : step E st q rid ≠ st rid) :
    ∃ r r' : Record,
      st rid = some r ∧ step E st q rid = some r' ∧
        r'.tenant = r.tenant ∧ E.member q.user r.tenant = true := by
  have hrid : rid = q.target :=
    Classical.byContradiction fun hcon => hne (step_eq_of_ne E st q hcon)
  subst hrid
  have hauth : authorized E st q = true := by
    cases hc : authorized E st q
    · exact absurd (by rw [step_eq_of_unauthorized E st q hc]) hne
    · rfl
  obtain ⟨hm, v, hv⟩ := of_authorized E st q hauth
  refine ⟨⟨q.tenant, v⟩, ⟨q.tenant, q.value⟩, hv, ?_, rfl, hm⟩
  unfold step
  rw [if_pos hauth, Store.update_self]

/-- **Member check prevents cross-tenant writes.**

No location is ever the site of a cross-tenant write: whenever the isolation
engine actually modifies a location `rid`, that location held a record `r`, the
acting user is a member of `r`'s owning tenant, and the new record stored there
is owned by the very same tenant.  Hence no record can be written on behalf of a
user outside its tenant, and no write can re-home a record into another
tenant. -/
theorem member_check_prevents_cross_tenant_write
    (E : Env) (st : Store) (q : Req) (rid : ResId) :
    ¬ CrossTenantWrite E st q rid := by
  rintro ⟨hne, hbad⟩
  obtain ⟨r, r', hr, hs, ht, hm⟩ := modified_location_is_own_tenant E st q rid hne
  rcases hbad r hr with hmem | hten
  · rw [hm] at hmem; exact Bool.noConfusion hmem
  · exact hten r' hs ht

/-- A user who is not a member of the tenant owning a record cannot change that
record. -/
theorem no_write_without_membership
    (E : Env) (st : Store) (q : Req) (rid : ResId) (r : Record)
    (hr : st rid = some r) (hm : E.member q.user r.tenant = false) :
    step E st q rid = st rid := by
  refine Classical.byContradiction fun hne => ?_
  obtain ⟨r₀, _, hr₀, _, _, hmem⟩ := modified_location_is_own_tenant E st q rid hne
  rw [hr] at hr₀
  cases hr₀
  rw [hm] at hmem
  exact Bool.noConfusion hmem

/-- Records never change owner. -/
theorem step_preserves_owner
    (E : Env) (st : Store) (q : Req) (rid : ResId) (r : Record) (hr : st rid = some r) :
    ∃ r' : Record, step E st q rid = some r' ∧ r'.tenant = r.tenant := by
  by_cases hne : step E st q rid = st rid
  · exact ⟨r, by rw [hne, hr], rfl⟩
  · obtain ⟨r₀, r', hr₀, hs, ht, _⟩ := modified_location_is_own_tenant E st q rid hne
    rw [hr] at hr₀
    cases hr₀
    exact ⟨r', hs, ht⟩

/-- Locations holding no record are never populated by a write. -/
theorem step_no_creation
    (E : Env) (st : Store) (q : Req) (rid : ResId) (hr : st rid = none) :
    step E st q rid = none := by
  by_cases hne : step E st q rid = st rid
  · rw [hne, hr]
  · obtain ⟨r, _, hr₀, _, _, _⟩ := modified_location_is_own_tenant E st q rid hne
    rw [hr] at hr₀
    exact absurd hr₀.symm (by simp)

/-! ## Completeness (the guard does not over-block) -/

/-- An authorized write does take effect. -/
theorem authorized_write_succeeds
    (E : Env) (st : Store) (q : Req) (h : authorized E st q = true) :
    step E st q q.target = some ⟨q.tenant, q.value⟩ := by
  unfold step
  rw [if_pos h, Store.update_self]

/-- The guard passes exactly when the acting user is a member of the claimed
tenant and the target record exists and belongs to that tenant. -/
theorem authorized_characterization (E : Env) (st : Store) (q : Req) :
    authorized E st q = true ↔
      E.member q.user q.tenant = true ∧ ∃ v : Value, st q.target = some ⟨q.tenant, v⟩ := by
  refine ⟨of_authorized E st q, ?_⟩
  rintro ⟨hm, v, hv⟩
  rw [authorized, Bool.and_eq_true]
  refine ⟨hm, ?_⟩
  unfold targetRecord
  rw [hv]
  simp

end PCA.WriteIntegrity

