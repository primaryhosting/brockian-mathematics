import Mathlib

/-!
# Integral Sinc Sq
Category: C Integral
Target: Zeta23Scaffold.integral_sinc_sq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Classical
open scoped FourierTransform

open MeasureTheory Complex

set_option maxHeartbeats 1000000

namespace Zeta23Scaffold

/-! ## The tent function and its Fourier transform

The proof of `∫ (sin x / x) ^ 2 dx = π` goes through Fourier inversion applied to the
tent (triangle) function `x ↦ max 0 (1 - |x|)`, whose Fourier transform is
`w ↦ (sin (π w) / (π w)) ^ 2`. -/

/-- The triangle (tent) function `x ↦ max 0 (1 - |x|)`, viewed as a complex-valued function. -/

lemma sq_sin_div_le (t : ℝ) : (Real.sin t / t) ^ 2 ≤ 2 * (1 + t ^ 2)⁻¹ := by
  rcases eq_or_ne t 0 with rfl | ht
  · norm_num
  have ht2 : 0 < t ^ 2 := by positivity
  have h1 : (0 : ℝ) < 1 + t ^ 2 := by positivity
  have hs1 : Real.sin t ^ 2 ≤ t ^ 2 := Real.sin_sq_le_sq
  have hs2 : Real.sin t ^ 2 ≤ 1 := Real.sin_sq_le_one t
  have hs0 : (0 : ℝ) ≤ Real.sin t ^ 2 := sq_nonneg _
  rw [div_pow, mul_comm 2 _, ← div_eq_inv_mul, div_le_div_iff₀ ht2 h1]
  nlinarith

