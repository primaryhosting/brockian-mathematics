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

lemma w7_pow_mul (k : ℕ) : w7 ^ k * w7 ^ (6 * k) = 1 := by
  rw [← pow_add]
  have h : k + 6 * k = 7 * k := by ring
  rw [h, pow_mul, w7_pow_seven, one_pow]

