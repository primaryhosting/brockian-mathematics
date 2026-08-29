/-
# Integral Sinc Sq
Category: C Integral
Target: Zeta23Scaffold.integral_sinc_sq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Integral Sinc Sq
Category: C Integral
Target: Zeta23Scaffold.integral_sinc_sq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The normalization integral of the sine kernel,
`∫ x : ℝ, (sin x / x) ^ 2 = π`.

The proof computes the Fourier transform of the triangle function
`tri x = max (1 - |x|) 0`, which is `w ↦ sinc (π w) ^ 2`, and then applies the
Fourier inversion formula at `0`.

Note that in Lean `sin 0 / 0 = 0`, so the integrand of the main statement differs from the
continuous extension `sinc` only on the null set `{0}`; the value of the integral is unaffected.
-/

open MeasureTheory Real Complex
open scoped FourierTransform

namespace Zeta23Scaffold

/-- The triangle function `x ↦ max (1 - |x|) 0`, viewed as a complex-valued function on `ℝ`. -/

lemma integral_sinc_pi_mul_sq : ∫ w : ℝ, Real.sinc (π * w) ^ 2 = 1 := by
  have hinv := tri_integrable.fourierInv_fourier_eq (v := (0:ℝ)) integrable_fourier_tri
    (tri_continuous.continuousAt)
  rw [Real.fourierInv_eq, tri_zero] at hinv
  simp only [inner_zero_right, AddChar.map_zero_eq_one, one_smul, fourier_tri] at hinv
  rw [integral_complex_ofReal] at hinv
  exact_mod_cast hinv

/-- The normalization integral of the sine kernel: `∫ x : ℝ, (sin x / x) ^ 2 = π`. -/
