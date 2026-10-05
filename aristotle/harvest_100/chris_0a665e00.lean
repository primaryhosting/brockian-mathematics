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
noncomputable def Hwin (lam : ℝ) : ℝ := 2 - 1 / lam - lam / 3

/-- The diagonal quantity `H_d(λ) = (1 + H(λ))/2`. -/
noncomputable def Hd (lam : ℝ) : ℝ := (1 + Hwin lam) / 2

/-- The comparison function `F(λ) = λ / (1 + λ²/3)`. -/
noncomputable def Fwin (lam : ℝ) : ℝ := lam / (1 + lam ^ 2 / 3)

/-- The denominator `1 + λ²/3` is positive. -/
lemma Fwin_denom_pos (lam : ℝ) : 0 < 1 + lam ^ 2 / 3 := by positivity

/-- The auxiliary quadratic `λ² - 3λ + 3` is strictly positive. -/
lemma aux_quadratic_pos (lam : ℝ) : 0 < lam ^ 2 - 3 * lam + 3 := by
  nlinarith [sq_nonneg (2 * lam - 3)]

/-- `0 ≤ H(λ)` is equivalent to the sign condition `0 ≤ 6λ - 3 - λ²`, for `λ > 0`. -/
lemma Hwin_nonneg_iff (lam : ℝ) (hlam : 0 < lam) :
    0 ≤ Hwin lam ↔ 0 ≤ 6 * lam - 3 - lam ^ 2 := by
  rw [Hwin]
  rw [show (2 : ℝ) - 1 / lam - lam / 3 = (6 * lam - 3 - lam ^ 2) / (3 * lam) by
    field_simp; ring]
  exact (le_div_iff₀ (by positivity)).symm.trans <| by
    constructor <;> intro h <;> nlinarith

/-- `F(λ) ≤ H_d(λ)` is equivalent to the sign condition `0 ≤ 6λ - 3 - λ²`, for `λ > 0`. -/
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
theorem Hd_ge_Fwin_iff (lam : ℝ) (hlam : 0 < lam) (hlam1 : lam ≤ 1) :
    Fwin lam ≤ Hd lam ↔ 0 ≤ Hwin lam :=
  (Fwin_le_Hd_iff_sign lam hlam).trans (Hwin_nonneg_iff lam hlam).symm

/-- The equivalence in fact holds for every `λ > 0`, with no upper bound on `λ`. -/
theorem Hd_ge_Fwin_iff_of_pos (lam : ℝ) (hlam : 0 < lam) :
    Fwin lam ≤ Hd lam ↔ 0 ≤ Hwin lam :=
  (Fwin_le_Hd_iff_sign lam hlam).trans (Hwin_nonneg_iff lam hlam).symm

end Zeta23Scaffold

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

