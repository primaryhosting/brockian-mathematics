/-!
# Huckel C 15
Category: Chemistry
Target: Chem.huckel_C15
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

open Finset

/-- A primitive 15-th root of unity. -/

lemma ee_add_ee_neg (k : ZMod 15) :
    ee k + ee (-k) = 2 * Real.cos (2 * Real.pi * k.val / 15) := by
  set θ : ℝ := 2 * Real.pi * k.val / 15 with hθ
  have h1 : ee k = Complex.exp ((θ : ℂ) * Complex.I) := by
    rw [ee, zeta, ← Complex.exp_nat_mul]
    congr 1
    push_cast [hθ]
    ring
  have h2 : ee (-k) = Complex.exp (-((θ : ℂ) * Complex.I)) := by
    have hmul := ee_mul_neg k
    rw [h1] at hmul
    have hne : Complex.exp ((θ : ℂ) * Complex.I) ≠ 0 := Complex.exp_ne_zero _
    field_simp [Complex.exp_neg]
    linear_combination hmul
  rw [h1, h2, Complex.exp_mul_I, ← neg_mul, Complex.exp_mul_I]
  simp [Complex.cos_neg, Complex.sin_neg, ← Complex.ofReal_cos]
  ring

/-- The adjacency matrix of the cycle graph `C₁₅`, with vertices indexed by `ZMod 15`. -/
