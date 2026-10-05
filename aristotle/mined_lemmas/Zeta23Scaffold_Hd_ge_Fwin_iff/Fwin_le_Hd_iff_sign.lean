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

lemma Fwin_le_Hd_iff_sign (lam : ℝ) (hlam : 0 < lam) :
    Fwin lam ≤ Hd lam ↔ 0 ≤ 6 * lam - 3 - lam ^ 2 := by
  have hden : (0 : ℝ) < 1 + lam ^ 2 / 3 := Fwin_denom_pos lam
  have hq : 0 < lam ^ 2 - 3 * lam + 3 := aux_quadratic_pos lam
  rw [Fwin, Hd, Hwin, div_le_div_iff₀ hden (by norm_num : (0:ℝ) < 2)]
  constructor
  · intro h
    have h' : lam * 2 * (3 * lam) ≤ (1 + (2 - 1 / lam - lam / 3)) * (1 + lam ^ 2 / 3) * (3 * lam) :=
      by nlinarith
    have hinv : lam * (1 / lam) = 1 := by field_simp
    nlinarith [hq, hinv]
  · intro h
    have hinv : lam * (1 / lam) = 1 := by field_simp
    rw [← sub_nonneg]
    have key : ((1 + (2 - 1 / lam - lam / 3)) * (1 + lam ^ 2 / 3) - lam * 2) * (3 * lam)
        = (6 * lam - 3 - lam ^ 2) * (lam ^ 2 - 3 * lam + 3) := by
      field_simp; ring
    nlinarith [key, mul_nonneg h hq.le]

/-- **Main statement.** For `0 < λ ≤ 1`, `F(λ) ≤ H_d(λ)` if and only if `0 ≤ H(λ)`.
(The hypothesis `λ ≤ 1` was requested in the statement; the proof shows it is not needed.) -/
