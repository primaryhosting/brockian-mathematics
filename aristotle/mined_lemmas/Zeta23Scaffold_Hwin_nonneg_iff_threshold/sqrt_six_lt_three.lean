/-
# Hwin Nonneg Iff Threshold
Category: A Assembly
Target: Zeta23Scaffold.Hwin_nonneg_iff_threshold
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Zeta23Scaffold

/-- The "window" function `H(λ) = 2 - 1/λ - λ/3`. -/

lemma sqrt_six_lt_three : Real.sqrt 6 < 3 := by
  have : Real.sqrt 6 < Real.sqrt 9 := by
    apply Real.sqrt_lt_sqrt <;> norm_num
  have h9 : Real.sqrt 9 = 3 := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 3)]
  linarith [h9 ▸ this]

/-- `H(λ) ≥ 0` iff `λ ≥ 3 - √6` on `0 < λ ≤ 1`. -/
