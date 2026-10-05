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

theorem Hd_ge_Fwin_iff_of_pos (lam : ℝ) (hlam : 0 < lam) :
    Fwin lam ≤ Hd lam ↔ 0 ≤ Hwin lam := by
  have hq : 0 < lam ^ 2 - 3 * lam + 3 := by nlinarith [sq_nonneg (2 * lam - 3)]
  have hden : 0 < 6 * lam * (3 + lam ^ 2) := by positivity
  rw [← sub_nonneg, Hd_sub_Fwin_eq lam hlam, Hwin_nonneg_iff lam hlam,
    le_div_iff₀ hden]
  constructor
  · intro h
    nlinarith [h, hq]
  · intro h
    nlinarith [h, hq]

/-- `H_d(λ) ≥ F(λ)` iff `H(λ) ≥ 0` on `0 < λ ≤ 1` (preprint eq. (1.3), third line,
first equivalence).  The hypothesis `lam ≤ 1` is not needed for the argument, but is
kept here as it appears in the source statement; see `Hd_ge_Fwin_iff_of_pos` for the
version assuming only `0 < lam`. -/
