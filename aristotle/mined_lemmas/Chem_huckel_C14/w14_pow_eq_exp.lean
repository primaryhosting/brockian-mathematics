/-
# Huckel C 14
Category: Chemistry
Target: Chem.huckel_C14
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 14
Category: Chemistry
Target: Chem.huckel_C14
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Matrix Polynomial SimpleGraph

/-- The adjacency matrix (Hückel matrix, with `α = 0`, `β = 1`) of the cycle graph `C₁₄`. -/

lemma w14_pow_eq_exp (m : ℕ) :
    w14 ^ m = Complex.exp ((2 * Real.pi * m / 14 : ℝ) * Complex.I) := by
  rw [w14, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

