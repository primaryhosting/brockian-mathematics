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

lemma tri_integrable : Integrable tri := by
  have hsupp : Function.support tri ⊆ Set.Icc (-1) 1 := by
    intro x hx
    simp only [Function.mem_support] at hx
    by_contra h
    refine hx (tri_eq_zero ?_)
    simp only [Set.mem_Icc, not_and_or, not_le] at h
    rcases h with h | h
    · rw [le_abs]; right; linarith
    · rw [le_abs]; left; linarith
  exact tri_continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_support_subset_isCompact isCompact_Icc hsupp)

/-- `sinc ^ 2` is integrable on `ℝ`: it is bounded by `2 / (1 + x ^ 2)`. -/
