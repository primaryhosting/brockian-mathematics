/-
# Huckel C 18
Category: Chemistry
Target: Chem.huckel_C18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 18
Category: Chemistry
Target: Chem.huckel_C18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Matrix SimpleGraph Complex

/-- The primitive 18-th root of unity `exp(2πi/18)`. -/

lemma adj_mul_V : (cycleGraph 18).adjMatrix ℂ * V = V * D := by
  ext j k
  rw [SimpleGraph.adjMatrix_mul_apply, D, Matrix.mul_diagonal]
  have hnb : (cycleGraph 18).neighborFinset j = {j - 1, j + 1} :=
    cycleGraph_neighborFinset (n := 16) (v := j)
  have hne : j - 1 ≠ j + 1 := by
    intro h
    rw [sub_eq_add_neg] at h
    exact absurd (add_left_cancel h) (by decide)
  rw [hnb, Finset.sum_pair hne]
  have h1 : j - 1 = j + 17 := by
    rw [sub_eq_add_neg]
    congr 1
  rw [h1, V_apply, V_apply, V_apply]
  have e1 : ((j + 17 : Fin 18) : ℕ) * (k : ℕ) % 18 = ((j : ℕ) + 17) * (k : ℕ) % 18 := by
    rw [Fin.val_add]
    simp [Nat.mul_mod, Nat.add_mod]
  have e2 : ((j + 1 : Fin 18) : ℕ) * (k : ℕ) % 18 = ((j : ℕ) + 1) * (k : ℕ) % 18 := by
    rw [Fin.val_add]
    simp [Nat.mul_mod, Nat.add_mod]
  rw [om_pow_congr e1, om_pow_congr e2]
  have expand1 : ((j : ℕ) + 17) * (k : ℕ) = (j : ℕ) * (k : ℕ) + 17 * (k : ℕ) := by ring
  have expand2 : ((j : ℕ) + 1) * (k : ℕ) = (j : ℕ) * (k : ℕ) + (k : ℕ) := by ring
  rw [expand1, expand2, pow_add, pow_add, ← om_pow_add_inv k]
  ring

/-- **Hückel theory for the C₁₈ annulene.**
The eigenvalues of the adjacency matrix of the cycle graph `C₁₈` are exactly the
numbers `2 cos(2πk/18)` for `k = 0, …, 17`. -/
