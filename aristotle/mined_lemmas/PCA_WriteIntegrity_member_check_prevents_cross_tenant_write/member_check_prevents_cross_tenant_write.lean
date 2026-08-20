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
