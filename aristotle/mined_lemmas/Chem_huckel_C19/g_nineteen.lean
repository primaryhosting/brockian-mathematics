/-
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Finset

/-- `g n = exp (2πi n / 19)`, the basic 19-th root of unity raised to `n`. -/

lemma g_nineteen : g 19 = 1 := by
  have h : (2 * (Real.pi : ℂ) * Complex.I * (19 : ℕ) / 19) = 2 * (Real.pi : ℂ) * Complex.I := by
    push_cast; ring
  rw [g, h, Complex.exp_two_pi_mul_I]

