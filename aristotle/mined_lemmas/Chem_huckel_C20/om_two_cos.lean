/-
# Huckel C 20
Category: Chemistry
Target: Chem.huckel_C20
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: Lean 4 does not permit a module docstring `/-! ... -/` before the `import`
line, so the required header appears here as an ordinary block comment.)
-/

import Mathlib

namespace Chem

open Complex Matrix

/-! ### The primitive 20-th root of unity and the associated character -/

/-- The primitive 20-th root of unity `exp (2πi/20)`. -/

lemma om_two_cos (m : ℕ) :
    om ^ m + om ^ (19 * m) = 2 * (Real.cos (2 * Real.pi * m / 20) : ℂ) := by
  have h1 : om ^ m * om ^ (19 * m) = 1 := by
    rw [← pow_add]
    have h : m + 19 * m = 20 * m := by ring
    rw [h, pow_mul, om_pow20, one_pow]
  have hne : om ^ m ≠ 0 := by simp [om, Complex.exp_ne_zero]
  have h2 : om ^ (19 * m) = (om ^ m)⁻¹ := by
    field_simp at h1 ⊢
    linear_combination h1
  rw [h2, om_pow_eq_exp, ← Complex.exp_neg, Complex.ofReal_cos, Complex.two_cos]
  ring_nf

/-- The standard additive character of `ZMod 20` with values in `ℂ`. -/
