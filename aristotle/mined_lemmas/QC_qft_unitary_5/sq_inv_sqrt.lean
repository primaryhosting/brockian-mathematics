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

namespace QC

/-- The primitive `N`-th root of unity `exp (2 π i / N)`. -/

lemma sq_inv_sqrt (N : ℕ) :
    ((Real.sqrt N : ℝ) : ℂ)⁻¹ * ((Real.sqrt N : ℝ) : ℂ)⁻¹ = ((N : ℂ))⁻¹ := by
  rw [← mul_inv, ← Complex.ofReal_mul, ← Real.sqrt_mul_self (by positivity : (0:ℝ) ≤ (N:ℝ))]
  norm_num

/-- The `N × N` QFT matrix is unitary. -/
