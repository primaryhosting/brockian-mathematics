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

lemma om_pow_mul_mod (a b : ℕ) : om ^ ((a % 15) * b) = om ^ (a * b) := by
  rw [← om_pow_mod ((a % 15) * b), ← om_pow_mod (a * b), Nat.mod_mul_mod]

