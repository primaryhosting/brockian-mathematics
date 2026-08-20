/-
# Huckel C 7
Category: Chemistry
Target: Chem.huckel_C7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

open Complex Matrix

/-- The adjacency matrix of the cycle graph `C₇` (the Hückel matrix of a 7-membered
ring, in units where α = 0 and β = 1): the vertices are `Fin 7` and `i` is adjacent to
`i + 1` and `i - 1`, the arithmetic being modulo 7. -/

lemma w7_pow_inv (k : ℕ) : (w7 ^ k)⁻¹ = w7 ^ (6 * k) :=
  (eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact w7_pow_mul k)).symm

