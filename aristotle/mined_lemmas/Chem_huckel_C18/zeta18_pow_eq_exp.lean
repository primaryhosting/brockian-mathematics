/-!
# Huckel C 18
Category: Chemistry
Target: Chem.huckel_C18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Complex Polynomial Matrix SimpleGraph

namespace Chem

/-- The primitive 18-th root of unity `exp (2πi/18)`. -/

lemma zeta18_pow_eq_exp (k : ℕ) :
    zeta18 ^ k = Complex.exp (((2 * Real.pi * k / 18 : ℝ) : ℂ) * Complex.I) := by
  rw [zeta18, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- `ζ^{-k} + ζ^{k} = 2 cos (2πk/18)`. -/
