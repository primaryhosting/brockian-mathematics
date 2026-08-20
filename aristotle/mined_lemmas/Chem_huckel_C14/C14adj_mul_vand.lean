/-
# Huckel C 14
Category: Chemistry
Target: Chem.huckel_C14
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 14
Category: Chemistry
Target: Chem.huckel_C14
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Matrix Polynomial SimpleGraph

/-- The adjacency matrix (Hückel matrix, with `α = 0`, `β = 1`) of the cycle graph `C₁₄`. -/

lemma C14adj_mul_vand : C14adj * C14vand = C14vand * Matrix.diagonal C14eigval := by
  ext i k
  rw [Matrix.mul_apply, Matrix.mul_diagonal]
  have hterm : ∀ j : Fin 14, C14adj i j * C14vand j k
      = (if j = i + 1 then C14vand j k else 0) + (if j = i - 1 then C14vand j k else 0) := by
    intro j
    rw [C14adj_apply]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ (i + 1) (fun j => C14vand j k),
    Finset.sum_ite_eq' Finset.univ (i - 1) (fun j => C14vand j k)]
  simp only [Finset.mem_univ, if_true]
  rw [C14vand_succ, C14vand_pred, ← mul_add, w14_pow_add_pow]

