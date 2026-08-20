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

lemma Q_mul_P : Q * P = 1 := by
  ext k k'
  rw [Matrix.mul_apply]
  have : ∀ j : Fin 15, Q k j * P j k'
      = (15 : ℂ)⁻¹ * (om ^ (k'.val * j.val) * (om ^ (j.val * k.val))⁻¹) := by
    intro j
    simp only [P, Q, mul_comm k'.val j.val]
    ring
  rw [Finset.sum_congr rfl (fun j _ => this j), ← Finset.mul_sum, key_sum]
  by_cases h : k = k'
  · simp [h, Matrix.one_apply]
  · simp [h, Ne.symm h]

