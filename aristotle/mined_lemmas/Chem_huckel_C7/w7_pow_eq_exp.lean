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

lemma w7_pow_eq_exp (k : ℕ) :
    w7 ^ k = Complex.exp (((2 * Real.pi * k / 7 : ℝ) : ℂ) * Complex.I) := by
  rw [w7, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- `2 cos(2πk/7)` expressed through the 7th root of unity `w7`. -/
