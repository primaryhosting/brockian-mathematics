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
