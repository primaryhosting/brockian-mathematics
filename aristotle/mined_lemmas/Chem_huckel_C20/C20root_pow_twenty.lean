/-
# Huckel C 20
Category: Chemistry
Target: Chem.huckel_C20
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open Complex Matrix Polynomial

namespace Chem

/-- The adjacency matrix of the cycle graph `C₂₀`, with vertices indexed by `ZMod 20`:
vertex `i` is adjacent exactly to `i + 1` and `i - 1`.  In Hückel theory (with `α = 0`,
`β = 1`) this is the Hückel matrix of the annulene `C₂₀`. -/

lemma C20root_pow_twenty (k : ZMod 20) : (C20root k) ^ 20 = 1 := by
  rw [C20root, ← Complex.exp_nat_mul]
  have h : ((20 : ℕ) : ℂ) * (((2 * Real.pi * (k.val : ℝ) / 20 : ℝ) : ℂ) * Complex.I)
      = ((k.val : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast; ring
  rw [h, Complex.exp_int_mul_two_pi_mul_I]

