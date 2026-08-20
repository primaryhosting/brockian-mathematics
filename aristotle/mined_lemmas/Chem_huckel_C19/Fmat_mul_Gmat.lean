/-
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open Complex (I)
open Matrix

namespace Chem

/-- The primitive 19-th root of unity `exp (2πi/19)`. -/

theorem Fmat_mul_Gmat : Fmat * Gmat = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  have hterm : ∀ k : Fin 19, Fmat i k * Gmat k j = (19 : ℂ)⁻¹ * ee (k * (i - j)) := by
    intro k
    simp only [Fmat, Gmat, Matrix.of_apply]
    rw [show ee (i * k) * ((19 : ℂ)⁻¹ * ee (-(k * j)))
        = (19 : ℂ)⁻¹ * (ee (i * k) * ee (-(k * j))) by ring, ← ee_add]
    congr 2
    rw [mul_comm i k, ← mul_neg, ← mul_add, ← sub_eq_add_neg]
  rw [Finset.sum_congr rfl (fun k _ => hterm k), ← Finset.mul_sum, sum_ee]
  by_cases h : i = j
  · subst h
    norm_num
  · rw [if_neg (sub_ne_zero_of_ne h), Matrix.one_apply_ne h, mul_zero]

