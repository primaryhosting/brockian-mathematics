/-
# Huckel C 9
Category: Chemistry
Target: Chem.huckel_C9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 9
Category: Chemistry
Target: Chem.huckel_C9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
open Complex Polynomial SimpleGraph

namespace Chem

/-- A primitive `9`-th root of unity. -/

theorem ff_exp (k : ZMod 9) :
    ff k = Complex.exp (((2 * Real.pi * k.val / 9 : ℝ) : ℂ) * Complex.I) := by
  rw [ff, zeta, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- The `k`-th eigenvalue is `2 cos (2πk/9)`. -/
