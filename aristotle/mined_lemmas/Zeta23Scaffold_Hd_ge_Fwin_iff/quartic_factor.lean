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

theorem quartic_factor (lam : ℝ) :
    lam ^ 4 - 9 * lam ^ 3 + 24 * lam ^ 2 - 27 * lam + 9
      = (lam ^ 2 - 6 * lam + 3) * (lam ^ 2 - 3 * lam + 3) := by
  ring

/-- `H_d(λ) ≥ F(λ)` iff `H(λ) ≥ 0`, for every `λ > 0`.

This is the unconditional form of the equivalence in eq. (1.3), third line, first equivalence:
the extra restriction `λ ≤ 1` is not needed. -/
