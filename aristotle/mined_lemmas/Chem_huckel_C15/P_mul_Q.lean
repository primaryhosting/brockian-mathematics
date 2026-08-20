/-
# Huckel C 15
Category: Chemistry
Target: Chem.huckel_C15
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 15
Category: Chemistry
Target: Chem.huckel_C15
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The Hückel model for the cyclic polyene `C₁₅` has Hamiltonian `α + β A`, where `A` is the
adjacency matrix of the cycle graph `C₁₅`.  We show that the spectrum of `A` is exactly
`{2 cos (2πk/15) : k = 0, …, 14}`, by explicitly diagonalizing `A` with the discrete
Fourier matrix.
-/

namespace Chem

open Complex Matrix SimpleGraph Finset

/-- A primitive 15-th root of unity. -/

lemma P_mul_Q : P * Q = 1 := by
  ext j j'
  rw [Matrix.mul_apply]
  have : ∀ k : Fin 15, P j k * Q k j'
      = (15 : ℂ)⁻¹ * (om ^ (j.val * k.val) * (om ^ (k.val * j'.val))⁻¹) := by
    intro k
    simp only [P, Q]
    ring
  rw [Finset.sum_congr rfl (fun k _ => this k), ← Finset.mul_sum, key_sum]
  by_cases h : j = j' <;> simp [h, Matrix.one_apply]

