/-
# Huckel C 15
Category: Chemistry
Target: Chem.huckel_C15
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
The Hückel (tight-binding) spectrum of the annulene `C₁₅`: the eigenvalues of the
adjacency matrix of the cycle graph `C₁₅` are exactly `2 cos (2πk/15)`, `k = 0, …, 14`.

Mathlib has the cycle graph (`SimpleGraph.cycleGraph`) and its adjacency matrix
(`SimpleGraph.adjMatrix`), the spectrum of a diagonal matrix (`spectrum_diagonal`) and
invariance of the spectrum under conjugation (`spectrum.units_conjugate`), but no
diagonalization of circulant matrices, so we build the discrete Fourier transform
matrix explicitly.
-/

namespace Chem

open Complex Matrix SimpleGraph

noncomputable section

/-- A primitive 15-th root of unity. -/

lemma Pmat_mul_Qmat : Pmat * Qmat = 1 := by
  ext j l
  rw [Matrix.mul_apply]
  have key : ∀ k : Fin 15, Pmat j k * Qmat k l
      = (15 : ℂ)⁻¹ * ((zeta ^ (j : ℕ)) * (zeta ^ (l : ℕ))⁻¹) ^ (k : ℕ) := by
    intro k
    have expand : ((zeta ^ (j : ℕ)) * (zeta ^ (l : ℕ))⁻¹) ^ (k : ℕ)
        = zeta ^ ((j : ℕ) * (k : ℕ)) * (zeta ^ ((k : ℕ) * (l : ℕ)))⁻¹ := by
      rw [mul_pow, inv_pow, ← pow_mul, ← pow_mul, mul_comm (l : ℕ) (k : ℕ)]
    simp only [Pmat, Qmat, Matrix.of_apply]
    rw [expand]
    ring
  rw [Finset.sum_congr rfl (fun k _ => key k), ← Finset.mul_sum, orthsum]
  by_cases h : j = l
  · subst h
    simp
  · rw [if_neg h, Matrix.one_apply_ne h, mul_zero]

