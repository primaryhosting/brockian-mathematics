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

theorem denied_write_is_noop (mem : MemberCheck Principal Tenant) (st : Store Tenant Key Val)
    (r : WriteReq Principal Tenant Key Val) (h : allowed mem st r = false) :
    applyWrite mem st r = st := by
  funext k; simp [applyWrite, h]

/-- Locality: a write only ever affects the key it targets. -/
