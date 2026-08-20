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

lemma two_cos_eq (k : ℕ) :
    ((2 * Real.cos (2 * Real.pi * k / 7) : ℝ) : ℂ) = w7 ^ k + (w7 ^ k)⁻¹ := by
  rw [w7_pow_eq_exp, ← Complex.exp_neg]
  have hneg : -(((2 * Real.pi * k / 7 : ℝ) : ℂ) * Complex.I)
      = ((-(2 * Real.pi * k / 7) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [hneg, Complex.exp_mul_I, Complex.exp_mul_I]
  push_cast
  simp [Complex.cos_neg, Complex.sin_neg]
  ring

/-- Action of the adjacency matrix of `C₇` on a vector. -/
