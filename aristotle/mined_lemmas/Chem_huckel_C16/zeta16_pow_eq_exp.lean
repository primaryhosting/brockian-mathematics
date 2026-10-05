/-
# Huckel C 16
Category: Chemistry
Target: Chem.huckel_C16
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 16
Category: Chemistry
Target: Chem.huckel_C16
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Matrix Polynomial SimpleGraph

/-- The adjacency matrix of the cycle graph `C₁₆` (the Hückel matrix of a
16-membered annulene, with `α = 0`, `β = 1`). -/

lemma zeta16_pow_eq_exp (m : ℕ) :
    zeta16 ^ m = Complex.exp (((2 * Real.pi * m / 16 : ℝ) : ℂ) * Complex.I) := by
  rw [zeta16, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- `ζ^m + ζ^{-m} = 2 cos (2πm/16)`. -/
