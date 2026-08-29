/-
# Huckel C 11
Category: Chemistry
Target: Chem.huckel_C11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 11
Category: Chemistry
Target: Chem.huckel_C11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix Complex Finset

namespace Chem

/-- The circulant form of the adjacency matrix of the cycle graph `C₁₁`,
with vertices indexed by `ZMod 11`. -/

theorem cycAdj_mul_fourierP : cycAdj * fourierP = fourierP * Matrix.diagonal eigVal := by
  ext i k
  rw [Matrix.mul_apply, Matrix.mul_diagonal]
  have hne : (i - 1 : ZMod 11) ≠ i + 1 := by
    intro h
    have h2 : (2 : ZMod 11) = 0 := by linear_combination -h
    exact absurd h2 (by decide)
  have key : ∀ j : ZMod 11, cycAdj i j * fourierP j k
      = (if j = i - 1 then fourierP j k else 0) + (if j = i + 1 then fourierP j k else 0) := by
    intro j
    have h1 : (i - j = 1) ↔ (j = i - 1) := by
      constructor <;> intro h <;> linear_combination -h
    have h2 : (i - j = -1) ↔ (j = i + 1) := by
      constructor <;> intro h <;> linear_combination -h
    simp only [cycAdj, Matrix.circulant_apply, h1, h2]
    by_cases ha : j = i - 1 <;> by_cases hb : j = i + 1 <;> simp [ha, hb] <;>
      first
        | (intro hc; exact absurd hc hne)
        | (intro hc; exact absurd hc.symm hne)
  rw [Finset.sum_congr rfl (fun j _ => key j), Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ (i - 1) (fun j => fourierP j k),
    Finset.sum_ite_eq' Finset.univ (i + 1) (fun j => fourierP j k)]
  simp only [Finset.mem_univ, if_true, fourierP, eigVal]
  rw [show (i - 1) * k = i * k + (-k) by ring, show (i + 1) * k = i * k + k by ring,
    AddChar.map_add_eq_mul, AddChar.map_add_eq_mul]
  ring

/-- The `k`-th eigenvalue is `2 cos (2πk/11)`. -/
