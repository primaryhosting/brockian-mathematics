import Mathlib

/-!
# Huckel C 11
Category: Chemistry
Target: Chem.huckel_C11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Complex Matrix Polynomial Finset

namespace Chem

/-- A primitive 11th root of unity. -/

lemma ee_add_ee_neg (k : Fin 11) : ee k + ee (-k) = huckelEigenvalue k := by
  have hprod : ee k * ee (-k) = 1 := by rw [← ee_add]; simp [ee_zero]
  have hne : ee k ≠ 0 := by rw [ee_exp]; exact Complex.exp_ne_zero _
  have h2 : ee (-k) = Complex.exp (-(((2 * Real.pi * (k : ℕ) / 11 : ℝ) : ℂ) * I)) := by
    rw [Complex.exp_neg, ← ee_exp]
    field_simp
    linear_combination hprod
  rw [huckelEigenvalue, ee_exp, h2, Complex.ofReal_cos, Complex.cos]
  ring_nf

