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

lemma C7adj_mulVec (v : Fin 7 → ℂ) (i : Fin 7) :
    (C7adj *ᵥ v) i = v (i + 1) + v (i - 1) := by
  have hn : (-1 : Fin 7) = 6 := by decide
  fin_cases i <;>
    simp [C7adj, Matrix.mulVec, dotProduct, Fin.sum_univ_seven, hn] <;> ring

/-- Going once around the cycle multiplies a geometric function by `c ^ 7`. -/
