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

/-- `Hwin lam = 2 - 1/lam - lam/3`. -/

lemma denom_pos (lam : ℝ) : (0 : ℝ) < 1 + lam ^ 2 / 3 := by
  nlinarith [sq_nonneg lam]

/-- `Hd lam - Fwin lam` has, for `lam > 0`, the sign of `6*lam - 3 - lam^2`,
since `6*lam*(3 + lam^2)*(Hd lam - Fwin lam) = (6*lam - 3 - lam^2)*(lam^2 - 3*lam + 3)`
and `lam^2 - 3*lam + 3 > 0`. -/
