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

namespace PCA
namespace WriteIntegrity

/-! ## Model

A minimal isolation engine for a multi-tenant store.

* Records live in a store and each record is owned by exactly one tenant.
* A principal carries the list of tenants it is a member of.
* A write request is executed only if the *member check* succeeds: the actor
  must be a member of the tenant owning the targeted record.

Everything below is stated for arbitrary stores and arbitrary traces of write
requests, so the guarantees are properties of the reference monitor itself.
-/

abbrev TenantId := Nat
abbrev RecordId := Nat
abbrev Value := Nat

/-- A principal, together with the tenants it belongs to. -/
structure Principal where
  pid : Nat
  tenants : List TenantId
deriving DecidableEq

/-- A stored record: its owning tenant and its payload. -/
structure Rec where
  owner : TenantId
  value : Value
deriving DecidableEq

/-- A store maps record identifiers to records (if present). -/
abbrev Store := RecordId → Option Rec

/-- Pointwise update of a store. -/
def upd (st : Store) (rid : RecordId) (v : Option Rec) : Store :=
  fun k => if k = rid then v else st k

@[simp] theorem upd_self (st : Store) (rid : RecordId) (v : Option Rec) :
    upd st rid v rid = v := by
  simp [upd]

theorem upd_of_ne (st : Store) (rid : RecordId) (v : Option Rec) {k : RecordId}
    (h : k ≠ rid) : upd st rid v k = st k := by
  simp [upd, h]

/-- A write request: an actor overwriting the value of a target record. -/
structure WriteReq where
  actor : Principal
  target : RecordId
  newValue : Value

/-- The owning tenant of a record, if the record exists. -/
def ownerOf (st : Store) (rid : RecordId) : Option TenantId :=
  (st rid).map (·.owner)

/-- The member check: the actor must belong to the tenant owning the target
record (and the target record must exist). -/
def memberCheck (st : Store) (w : WriteReq) : Bool :=
  match st w.target with
  | none => false
  | some r => w.actor.tenants.contains r.owner

/-- The reference monitor: a write takes effect only if the member check passes. -/
def step (st : Store) (w : WriteReq) : Store :=
  if memberCheck st w then
    upd st w.target ((st w.target).map (fun r => { r with value := w.newValue }))
  else
    st

/-- Executing a whole trace of write requests through the reference monitor. -/
def execTrace (st : Store) (ws : List WriteReq) : Store :=
  ws.foldl step st

@[simp] theorem execTrace_nil (st : Store) : execTrace st [] = st := rfl

@[simp] theorem execTrace_cons (st : Store) (w : WriteReq) (ws : List WriteReq) :
    execTrace st (w :: ws) = execTrace (step st w) ws := rfl

/-- Records other than the target are untouched by a step. -/
theorem step_eq_of_ne (st : Store) (w : WriteReq) {rid : RecordId} (h : rid ≠ w.target) :
    step st w rid = st rid := by
  unfold step
  split
  · exact upd_of_ne st w.target _ h
  · rfl

/-- A single step never changes the owner of a record. -/
theorem ownerOf_step (st : Store) (w : WriteReq) (rid : RecordId) :
    ownerOf (step st w) rid = ownerOf st rid := by
  by_cases h : rid = w.target
  · subst h
    unfold step ownerOf
    split
    · rw [upd_self]
      cases st w.target <;> simp
    · rfl
  · unfold ownerOf
    rw [step_eq_of_ne st w h]

/-- A whole trace never changes the owner of a record. -/
theorem ownerOf_execTrace (st : Store) (ws : List WriteReq) (rid : RecordId) :
    ownerOf (execTrace st ws) rid = ownerOf st rid := by
  induction ws generalizing st with
  | nil => rfl
  | cons w ws ih => rw [execTrace_cons, ih, ownerOf_step]

/-- **Soundness of the member check for one step.**  If a step modifies a record,
then the request targeted that record and its actor is a member of the tenant
owning that record. -/
theorem step_change_imp_member (st : Store) (w : WriteReq) {rid : RecordId} {t : TenantId}
    (howner : ownerOf st rid = some t) (h : step st w rid ≠ st rid) :
    w.target = rid ∧ t ∈ w.actor.tenants := by
  by_cases hne : rid = w.target
  · subst hne
    refine ⟨rfl, ?_⟩
    unfold step at h
    by_cases hc : memberCheck st w = true
    · unfold memberCheck at hc
      unfold ownerOf at howner
      cases hst : st w.target with
      | none =>
        rw [hst] at howner
        simp at howner
      | some r =>
        rw [hst] at howner hc
        simp only [Option.map_some] at howner
        have ht : r.owner = t := Option.some.inj howner
        subst ht
        simpa using hc
    · simp [hc] at h
  · exact absurd (step_eq_of_ne st w hne) h

/-- **Completeness of the member check for one step.**  If the actor is a member of
the tenant owning an existing target record, the write does take effect. -/
theorem step_apply_of_member (st : Store) (w : WriteReq) (r : Rec)
    (hst : st w.target = some r) (hmem : r.owner ∈ w.actor.tenants) :
    step st w w.target = some { r with value := w.newValue } := by
  unfold step memberCheck
  rw [hst]
  simp [hmem]

/-- **Main theorem: the member check prevents cross-tenant writes.**

If, after executing an arbitrary trace of write requests through the reference
monitor, the contents of a record owned by tenant `t` have changed, then the
trace must contain a write request that targeted that record and whose actor is
a member of tenant `t`.  Equivalently (see `non_member_cannot_write`), no
principal outside tenant `t` can ever affect the data of tenant `t`. -/
theorem member_check_prevents_cross_tenant_write
    (st : Store) (ws : List WriteReq) (rid : RecordId) (t : TenantId)
    (howner : ownerOf st rid = some t)
    (hchange : execTrace st ws rid ≠ st rid) :
    ∃ w ∈ ws, w.target = rid ∧ t ∈ w.actor.tenants := by
  induction ws generalizing st with
  | nil => exact absurd rfl hchange
  | cons w ws ih =>
    rw [execTrace_cons] at hchange
    by_cases hstep : step st w rid = st rid
    · have howner' : ownerOf (step st w) rid = some t := by
        rw [ownerOf_step]; exact howner
      have hchange' : execTrace (step st w) ws rid ≠ step st w rid := by
        rw [hstep]; exact hchange
      obtain ⟨w', hw', h1, h2⟩ := ih (step st w) howner' hchange'
      exact ⟨w', List.mem_cons_of_mem _ hw', h1, h2⟩
    · obtain ⟨h1, h2⟩ := step_change_imp_member st w howner hstep
      exact ⟨w, List.mem_cons_self, h1, h2⟩

/-- Corollary (isolation): if no actor in the trace is a member of tenant `t`,
then a record owned by `t` is left completely unchanged. -/
theorem non_member_cannot_write
    (st : Store) (ws : List WriteReq) (rid : RecordId) (t : TenantId)
    (howner : ownerOf st rid = some t)
    (hall : ∀ w ∈ ws, t ∉ w.actor.tenants) :
    execTrace st ws rid = st rid := by
  by_cases hchange : execTrace st ws rid = st rid
  · exact hchange
  · obtain ⟨w, hw, _, hmem⟩ :=
      member_check_prevents_cross_tenant_write st ws rid t howner hchange
    exact absurd hmem (hall w hw)

/-! ## Sanity checks: the model is not vacuous -/

section Demo

/-- A store with a single record `0` owned by tenant `7`. -/
def demoStore : Store := fun k => if k = 0 then some { owner := 7, value := 1 } else none

/-- An outsider: a member of tenant `9` only. -/
def outsider : Principal := { pid := 1, tenants := [9] }

/-- An insider: a member of tenant `7`. -/
def insider : Principal := { pid := 2, tenants := [7, 9] }

/-- The outsider's write is rejected: the record is unchanged. -/
example : step demoStore { actor := outsider, target := 0, newValue := 42 } 0
    = some { owner := 7, value := 1 } := by
  decide

/-- The insider's write goes through. -/
example : step demoStore { actor := insider, target := 0, newValue := 42 } 0
    = some { owner := 7, value := 42 } := by
  decide

end Demo

end WriteIntegrity
end PCA

