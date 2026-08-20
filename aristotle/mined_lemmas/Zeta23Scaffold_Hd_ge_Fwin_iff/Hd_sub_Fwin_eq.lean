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

theorem Hd_sub_Fwin_eq (lam : ℝ) (hlam : 0 < lam) :
    Hd lam - Fwin lam =
      (6 * lam - 3 - lam ^ 2) * (lam ^ 2 - 3 * lam + 3) / (6 * lam * (3 + lam ^ 2)) := by
  have h1 : lam ≠ 0 := ne_of_gt hlam
  have h2 : (0 : ℝ) < 3 + lam ^ 2 := by positivity
  have h3 : (0 : ℝ) < 1 + lam ^ 2 / 3 := by positivity
  unfold Hd Fwin Hwin
  field_simp
  ring

/-- Unconditional form: for every `λ > 0`, `F(λ) ≤ H_d(λ) ↔ 0 ≤ H(λ)`.
The auxiliary quadratic factor `λ² - 3λ + 3` has negative discriminant, hence is
positive, so the sign of `H_d(λ) - F(λ)` is exactly that of `6λ - 3 - λ² = 3λ·H(λ)`. -/
