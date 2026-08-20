/-
# Hd Ge Fwin Iff
Category: A Assembly
Target: Zeta23Scaffold.Hd_ge_Fwin_iff
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Zeta23Scaffold

/-- The window function `H(λ) = 2 - 1/λ - λ/3`. -/

lemma sq_sub_three_mul_add_three_pos (lam : ℝ) : 0 < lam ^ 2 - 3 * lam + 3 := by
  nlinarith [sq_nonneg (2 * lam - 3)]

/-- `1 + λ²/3 > 0`. -/
