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

lemma one_add_sq_div_three_pos (lam : ℝ) : 0 < 1 + lam ^ 2 / 3 := by positivity

/-- For `lam > 0`, the comparison `Fwin lam ≤ Hd lam` is equivalent to `0 ≤ Hwin lam`.

Indeed `Hwin lam = (6*lam - 3 - lam^2) / (3*lam)` and
`Hd lam - Fwin lam = (6*lam - 3 - lam^2) * (lam^2 - 3*lam + 3) / (6*lam*(3 + lam^2))`.
Since `lam > 0` and `lam^2 - 3*lam + 3 = (lam - 3/2)^2 + 3/4 > 0`, both quantities have the
sign of `6*lam - 3 - lam^2`. -/
