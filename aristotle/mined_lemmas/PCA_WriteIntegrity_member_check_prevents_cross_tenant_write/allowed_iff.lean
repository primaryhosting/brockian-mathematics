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
