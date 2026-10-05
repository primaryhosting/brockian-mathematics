/-
# Hd Ge Fwin Iff
Category: A Assembly
Target: Zeta23Scaffold.Hd_ge_Fwin_iff
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Hd Ge Fwin Iff
Category: A Assembly
Target: Zeta23Scaffold.Hd_ge_Fwin_iff
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Zeta23Scaffold

/-- The window function `H(λ) = 2 - 1/λ - λ/3`. -/

lemma quad_pos (lam : ℝ) : 0 < lam ^ 2 - 3 * lam + 3 := by
  nlinarith [sq_nonneg (2 * lam - 3)]

/-- `H_d(λ) ≥ F(λ)` iff `H(λ) ≥ 0`, for `0 < λ ≤ 1` (preprint eq. (1.3)). -/
