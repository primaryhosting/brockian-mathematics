import Mathlib
/-!
# Huckel C 8
Category: Chemistry
Target: Chem.huckel_C8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Complex Matrix Polynomial

namespace Chem

/-- A primitive 8-th root of unity. -/

lemma pow_cycle_ident (w : ℂ) (hw : w ^ 8 = 1) (i : Fin 8) :
    w ^ ((i + 1 : Fin 8) : ℕ) + w ^ ((i - 1 : Fin 8) : ℕ) = w ^ (i : ℕ) * (w + w⁻¹) := by
  have hinv : w⁻¹ = w ^ 7 := inv_eq_of_mul_eq_one_right (by linear_combination hw)
  rw [hinv]
  fin_cases i <;> norm_num [Fin.val_add, Fin.val_sub]
  · linear_combination -hw
  · linear_combination -w * hw
  · linear_combination -w ^ 2 * hw
  · linear_combination -w ^ 3 * hw
  · linear_combination -w ^ 4 * hw
  · linear_combination -w ^ 5 * hw
  · linear_combination -(1 + w ^ 6) * hw

/-- Multiplying by the adjacency matrix of `C₈` picks out the two cyclic neighbours. -/
