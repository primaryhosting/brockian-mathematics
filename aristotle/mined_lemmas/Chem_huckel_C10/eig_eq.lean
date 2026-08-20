/-
# Huckel C 10
Category: Chemistry
Target: Chem.huckel_C10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
(Note: Lean requires `import` to precede any module docstring `/-! ... -/`,
so this header is a plain block comment.)
-/

import Mathlib

namespace Chem

open Complex Matrix Polynomial

/-- A primitive 10-th root of unity. -/

lemma eig_eq (k : Fin 10) : eig k = zeta ^ (k : ℕ) + zeta ^ (9 * (k : ℕ)) := by
  have h1 : zeta ^ ((k : ℕ)) = Complex.exp (((2 * Real.pi * (k : ℕ) / 10 : ℝ) : ℂ) * I) := by
    rw [zeta, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hmul : zeta ^ ((k : ℕ)) * zeta ^ (9 * (k : ℕ)) = 1 := by
    rw [← pow_add, show (k : ℕ) + 9 * (k : ℕ) = 10 * (k : ℕ) from by ring, pow_mul,
      zeta_pow_ten, one_pow]
  have h2 : zeta ^ (9 * (k : ℕ)) = Complex.exp (-((2 * Real.pi * (k : ℕ) / 10 : ℝ) : ℂ) * I) := by
    have hinv : zeta ^ (9 * (k : ℕ)) = (zeta ^ ((k : ℕ)))⁻¹ := by
      have hne : zeta ^ ((k : ℕ)) ≠ 0 := by simp [zeta, Complex.exp_ne_zero]
      field_simp
      linear_combination hmul
    rw [hinv, h1, ← Complex.exp_neg]
    congr 1
    ring
  rw [eig, h1, h2, Complex.ofReal_cos]
  exact Complex.two_cos _

