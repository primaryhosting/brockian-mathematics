import Mathlib

/-!
# Integral Sinc Fourth
Category: C Integral
Target: Zeta23Scaffold.integral_sinc_fourth
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Zeta23Scaffold

open MeasureTheory Real FourierTransform intervalIntegral

/-! ## The tent function and its Fourier transform -/

/-- The tent (triangle) function, supported on `[-1, 1]`. -/

lemma integrable_sincSq : Integrable (fun ξ : ℝ => Real.sinc (π * ξ) ^ 2) := by
  have hb : Integrable (fun ξ : ℝ => 2 * (1 + (π * ξ) ^ 2)⁻¹) := by
    have h : Integrable (fun x : ℝ => (1 + (π * x) ^ 2)⁻¹) :=
      (integrable_comp_mul_left_iff (fun x : ℝ => (1 + x ^ 2)⁻¹) Real.pi_ne_zero).2
        integrable_inv_one_add_sq
    exact h.const_mul 2
  refine hb.mono' ?_ ?_
  · exact ((Real.continuous_sinc.comp (by fun_prop)).pow 2).aestronglyMeasurable
  · filter_upwards with ξ
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact sinc_sq_le _

