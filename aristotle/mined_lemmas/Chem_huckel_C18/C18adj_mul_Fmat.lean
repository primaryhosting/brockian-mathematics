import Mathlib
/-!
# Huckel C 18
Category: Chemistry
Target: Chem.huckel_C18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Matrix

/-- The adjacency matrix of the cycle graph `C₁₈`, with vertices indexed by `ZMod 18`:
two vertices are adjacent iff they differ by `1` modulo `18`. -/

lemma C18adj_mul_Fmat : C18adj * Fmat = Fmat * Dmat := by
  ext j k
  have hne : (j + 1 : ZMod 18) ≠ j - 1 := by
    intro h
    have : (2 : ZMod 18) = 0 := by linear_combination h
    exact absurd this (by decide)
  have hsplit : ∀ i : ZMod 18,
      C18adj j i * Fmat i k
        = (if i = j + 1 then Fmat i k else 0) + (if i = j - 1 then Fmat i k else 0) := by
    intro i
    simp only [C18adj, Matrix.of_apply]
    by_cases h1 : i = j + 1
    · subst h1; simp [hne]
    · by_cases h2 : i = j - 1
      · subst h2; simp [h1]
      · simp [h1, h2]
  rw [Matrix.mul_apply, Finset.sum_congr rfl fun i _ => hsplit i, Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ (j + 1) (fun i => Fmat i k),
    Finset.sum_ite_eq' Finset.univ (j - 1) (fun i => Fmat i k)]
  simp only [Finset.mem_univ, if_true]
  rw [Dmat, Matrix.mul_diagonal]
  simp only [Fmat, Matrix.of_apply]
  rw [← w_add_neg k, show (j + 1) * k = j * k + k by ring,
    show (j - 1) * k = j * k + -k by ring, w_add, w_add]
  ring

/-- The Hückel molecular orbitals: for each `k`, the vector `j ↦ exp (2πI jk/18)` is a nonzero
eigenvector of the adjacency matrix of `C₁₈` with eigenvalue `2 cos (2πk/18)`. -/
