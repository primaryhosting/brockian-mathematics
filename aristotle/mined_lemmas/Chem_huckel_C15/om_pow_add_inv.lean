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

lemma om_pow_add_inv (k : Fin 15) : om ^ k.val + (om ^ k.val)⁻¹ = lam k := by
  have h1 : om ^ k.val = Complex.exp (((2 * Real.pi * (k.val : ℝ) / 15 : ℝ) : ℂ) * Complex.I) := by
    rw [om, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [h1, ← Complex.exp_neg, lam, Complex.ofReal_cos, Complex.two_cos]
  ring_nf

/-- The adjacency matrix of the cycle graph `C₁₅`. -/
