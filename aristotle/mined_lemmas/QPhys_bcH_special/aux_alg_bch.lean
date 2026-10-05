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

/-
# Bc H Special
Category: Quantum Physics
Target: QPhys.bcH_special
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Bc H Special
Category: Quantum Physics
Target: QPhys.bcH_special
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open NormedSpace

namespace QPhys

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

omit [CompleteSpace 𝔸] in
/-- A function `ℝ → 𝔸` with everywhere vanishing derivative is constant. -/

theorem aux_alg_bch {R : Type*} [Ring R] (A B K q r s : R)
    (f1 : q * A = (A + K) * q) (f2 : r * B = (B + K) * r) (f3 : q * B = (B - K) * q)
    (f4 : K * q = q * K) :
    ((-(A + B)) * q * r + q * (A * r)) * s + (q * r) * (B * s) = K * (q * r * s) := by
  have e1 : q * (A * r) = (A + K) * q * r := by rw [← mul_assoc, f1]
  have e3 : q * (B + K) = B * q := by rw [mul_add, ← f4, f3]; noncomm_ring
  have e2 : (q * r) * (B * s) = (B * q * r) * s := by
    rw [mul_assoc q r, ← mul_assoc r B, f2, ← mul_assoc, ← mul_assoc, e3]
  rw [e1, e2]
  noncomm_ring

/-- The Baker-Campbell-Hausdorff formula in the special case of a central commutator:
if `[A, B]` commutes with both `A` and `B`, then `e^A e^B = e^{A + B + ½[A,B]}`. -/
