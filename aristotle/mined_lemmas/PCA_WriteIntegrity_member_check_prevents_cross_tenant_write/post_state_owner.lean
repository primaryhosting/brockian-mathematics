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
