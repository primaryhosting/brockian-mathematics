/-!
# Hd Ge Fwin Iff
Category: A Assembly
Target: Zeta23Scaffold.Hd_ge_Fwin_iff
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Zeta23Scaffold

/-- The window function `H(λ) = 2 - 1/λ - λ/3`. -/

lemma Fwin_denom_pos (lam : ℝ) : 0 < 1 + lam ^ 2 / 3 := by positivity

/-- The auxiliary quadratic `λ² - 3λ + 3` is strictly positive. -/
