/-
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Finset

/-- `g n = exp (2πi n / 19)`, the basic 19-th root of unity raised to `n`. -/

lemma z19_add_neg (x : ZMod 19) :
    z19 x + z19 (-x) = 2 * (Real.cos (2 * Real.pi * x.val / 19) : ℂ) := by
  set θ : ℝ := 2 * Real.pi * x.val / 19 with hθ
  have h1 : z19 x = Complex.exp ((θ : ℂ) * Complex.I) := by
    rw [z19, g, hθ]
    congr 1
    push_cast
    ring
  have h2 : z19 (-x) = Complex.exp (-(θ : ℂ) * Complex.I) := by
    have hprod := z19_neg_mul x
    have hx : Complex.exp ((θ : ℂ) * Complex.I) * Complex.exp (-(θ : ℂ) * Complex.I) = 1 := by
      rw [← Complex.exp_add]
      have hzero : (θ : ℂ) * Complex.I + -(θ : ℂ) * Complex.I = 0 := by ring
      rw [hzero, Complex.exp_zero]
    have hne : Complex.exp ((θ : ℂ) * Complex.I) ≠ 0 := Complex.exp_ne_zero _
    rw [h1] at hprod
    exact mul_left_cancel₀ hne (hprod.trans hx.symm)
  rw [h1, h2, Complex.ofReal_cos, Complex.cos]
  ring

/-- The adjacency matrix of the cycle graph `C₁₉`, with vertices indexed by `ZMod 19`. -/
