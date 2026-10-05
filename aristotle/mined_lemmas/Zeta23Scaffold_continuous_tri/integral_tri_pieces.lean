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

lemma integral_tri_pieces (z : ℂ) (hz : z ≠ 0) :
    (∫ x in (0:ℝ)..1, Complex.exp (z * x) * (1 - x))
      + (∫ x in (-1:ℝ)..0, Complex.exp (z * x) * (1 + x))
      = (Complex.exp z + Complex.exp (-z) - 2) / z ^ 2 := by
  have h1 := integral_expmul z ((1 + 1 / z) / z) (-1 / z) 0 1
  have h2 := integral_expmul z ((1 - 1 / z) / z) (1 / z) (-1) 0
  have e1 : ∀ x : ℝ, Complex.exp (z * x) * ((z * ((1 + 1 / z) / z) + (-1 / z)) + z * (-1 / z) * x)
      = Complex.exp (z * x) * (1 - x) := by
    intro x; congr 1; field_simp; ring
  have e2 : ∀ x : ℝ, Complex.exp (z * x) * ((z * ((1 - 1 / z) / z) + (1 / z)) + z * (1 / z) * x)
      = Complex.exp (z * x) * (1 + x) := by
    intro x; congr 1; field_simp; ring
  simp_rw [e1] at h1
  simp_rw [e2] at h2
  rw [h1, h2]
  push_cast
  field_simp
  simp only [mul_zero, Complex.exp_zero]
  ring

/-- Splitting `∫ exp (z x) * tri x` into the two linear pieces. -/
