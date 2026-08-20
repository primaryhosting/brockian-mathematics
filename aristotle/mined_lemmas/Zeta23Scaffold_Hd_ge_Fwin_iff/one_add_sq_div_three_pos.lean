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

lemma one_add_sq_div_three_pos (lam : ℝ) : 0 < 1 + lam ^ 2 / 3 := by positivity

/-- Key algebraic identity: after clearing the positive denominators `6λ` and `3 + λ²`,
the difference `H_d(λ) - F(λ)` has numerator `(6λ - 3 - λ²)(λ² - 3λ + 3)`,
while `H(λ)` has numerator `6λ - 3 - λ²`. -/
