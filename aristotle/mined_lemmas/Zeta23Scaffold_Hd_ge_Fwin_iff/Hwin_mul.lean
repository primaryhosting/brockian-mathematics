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

theorem Hwin_mul (lam : ℝ) (hlam : lam ≠ 0) :
    Hwin lam * (3 * lam) = 6 * lam - 3 - lam ^ 2 := by
  unfold Hwin
  field_simp
  ring

/-- Key algebraic identity: for `λ > 0`,
`H_d(λ) - F(λ) = (6λ - 3 - λ²)(λ² - 3λ + 3) / (6λ(3 + λ²))`. -/
