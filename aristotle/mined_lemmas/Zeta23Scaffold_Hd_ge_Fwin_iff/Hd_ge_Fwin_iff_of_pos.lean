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

theorem Hd_ge_Fwin_iff_of_pos (lam : ℝ) (hlam : 0 < lam) :
    Fwin lam ≤ Hd lam ↔ 0 ≤ Hwin lam := by
  have hq : 0 < lam ^ 2 - 3 * lam + 3 := by nlinarith [sq_nonneg (2 * lam - 3)]
  have hden : 0 < 6 * lam * (3 + lam ^ 2) := by positivity
  have hH : 0 ≤ Hwin lam ↔ 0 ≤ 6 * lam - 3 - lam ^ 2 := by
    rw [← Hwin_mul lam (ne_of_gt hlam)]
    exact (mul_nonneg_iff_of_pos_right (by positivity : (0:ℝ) < 3 * lam)).symm
  rw [← sub_nonneg, Hd_sub_Fwin_eq lam hlam, le_div_iff₀ hden, hH]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

/-- `H_d(λ) ≥ F(λ)` iff `H(λ) ≥ 0`, for `0 < λ ≤ 1`
(preprint eq. (1.3), third line, first equivalence).

The hypothesis `lam ≤ 1` is included as requested, but it is not needed: see
`Hd_ge_Fwin_iff_of_pos`, which gives the same equivalence for all `λ > 0`. -/
