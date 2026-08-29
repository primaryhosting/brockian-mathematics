/-
# Huckel C 5
Category: Chemistry
Target: Chem.huckel_C5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Huckel C 5
Category: Chemistry
Target: Chem.huckel_C5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset Matrix

namespace Chem

/-- A primitive fifth root of unity. -/

lemma C5adj_mul_F5 :
    C5adj * F5 = F5 * Matrix.diagonal huckelEigenvalue := by
  ext i k
  have hsplit : ∀ j : ZMod 5, C5adj i j * F5 j k
      = (if j = i + 1 then F5 j k else 0) + (if j = i - 1 then F5 j k else 0) := by
    have hne : (i + 1 : ZMod 5) ≠ i - 1 := by
      intro h
      have h2 : (2 : ZMod 5) = 0 := by linear_combination h
      exact absurd h2 (by decide)
    intro j
    by_cases h1 : j = i + 1
    · simp [C5adj, h1, hne]
    · by_cases h2 : j = i - 1
      · simp [C5adj, h2, hne.symm]
      · simp [C5adj, h1, h2]
  rw [Matrix.mul_apply, Finset.sum_congr rfl (fun j _ => hsplit j), Finset.sum_add_distrib,
    Finset.sum_ite_eq' univ (i + 1) (fun j => F5 j k),
    Finset.sum_ite_eq' univ (i - 1) (fun j => F5 j k)]
  simp only [Finset.mem_univ, if_true]
  rw [Matrix.mul_apply, Finset.sum_eq_single k (fun b _ hb => by simp [Matrix.diagonal, hb])
    (by simp)]
  simp only [F5, Matrix.diagonal_apply_eq]
  rw [show (i + 1) * k = i * k + k by ring, show (i - 1) * k = i * k + -k by ring,
    e5_add, e5_add, ← mul_add, e5_add_e5_neg]

/-! ### The characteristic determinant -/

