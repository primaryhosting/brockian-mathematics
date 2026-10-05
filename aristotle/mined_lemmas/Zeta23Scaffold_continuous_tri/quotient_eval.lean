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

lemma quotient_eval (w : ℝ) (hw : w ≠ 0) (z : ℂ) (hzdef : z = ((-2 * π * w : ℝ) : ℂ) * Complex.I) :
    (Complex.exp z + Complex.exp (-z) - 2) / z ^ 2
      = (((Real.sin (π * w) / (π * w)) ^ 2 : ℝ) : ℂ) := by
  have hpw : (π * w) ≠ 0 := mul_ne_zero Real.pi_ne_zero hw
  have hz2 : z ^ 2 = ((-(2 * π * w) ^ 2 : ℝ) : ℂ) := by
    rw [hzdef]; push_cast; ring_nf; simp [Complex.I_sq]
  have hexp : Complex.exp z + Complex.exp (-z) = ((2 * Real.cos (2 * π * w) : ℝ) : ℂ) := by
    rw [hzdef]
    push_cast
    rw [show (-2 * (π : ℂ) * (w : ℂ) * Complex.I)
        = ((2 * (π : ℂ) * (w : ℂ)) * Complex.I) * (-1) by ring]
    rw [show (((2 * (π : ℂ) * (w : ℂ)) * Complex.I) * (-1))
        = -((2 * (π : ℂ) * (w : ℂ)) * Complex.I) by ring]
    rw [neg_neg, add_comm]
    exact exp_add_exp_neg _
  rw [hexp, hz2]
  have hcos : 2 * Real.cos (2 * π * w) - 2 = -(4 * Real.sin (π * w) ^ 2) := by
    have h : Real.cos (2 * (π * w)) = 1 - 2 * Real.sin (π * w) ^ 2 := by
      rw [Real.cos_two_mul]
      nlinarith [Real.sin_sq_add_cos_sq (π * w)]
    rw [show 2 * π * w = 2 * (π * w) by ring, h]; ring
  rw [show ((2 * Real.cos (2 * π * w) : ℝ) : ℂ) - 2
      = (((2 * Real.cos (2 * π * w) - 2 : ℝ)) : ℂ) by push_cast; ring, hcos,
    ← Complex.ofReal_div]
  congr 1
  field_simp
  ring

/-- The Fourier transform of the tent function is `w ↦ (sin (π w) / (π w)) ^ 2`
(away from `w = 0`). -/
