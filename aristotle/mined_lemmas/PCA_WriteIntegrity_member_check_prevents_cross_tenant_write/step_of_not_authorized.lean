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

theorem step_of_not_authorized [DecidableEq Res] {pol : Policy Tenant User Res}
    {req : Request User Res Val} (st : Store Res Val)
    (h : authorized pol req = false) : step pol req st = st := by
  simp [step, h]

/-- An admitted request writes exactly its value at exactly its target. -/
