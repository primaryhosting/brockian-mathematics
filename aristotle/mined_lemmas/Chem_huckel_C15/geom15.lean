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

lemma geom15 (z : ℂ) (hz : z ^ 15 = 1) :
    ∑ k : Fin 15, z ^ (k : ℕ) = if z = 1 then 15 else 0 := by
  by_cases h : z = 1
  · simp [h]
  · rw [if_neg h, Fin.sum_univ_eq_sum_range (fun k => z ^ k) 15,
      geom_sum_eq h, hz, sub_self, zero_div]

/-- The discrete Fourier transform matrix for `C₁₅`. -/
