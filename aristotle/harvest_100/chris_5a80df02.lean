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
noncomputable def Hwin (lam : ℝ) : ℝ := 2 - 1 / lam - lam / 3

/-- `Hd lam = (1 + Hwin lam)/2`. -/
noncomputable def Hd (lam : ℝ) : ℝ := (1 + Hwin lam) / 2

/-- `Fwin lam = lam / (1 + lam^2/3)`. -/
noncomputable def Fwin (lam : ℝ) : ℝ := lam / (1 + lam ^ 2 / 3)

/-- The denominator `1 + lam^2/3` is positive. -/
lemma one_add_sq_div_three_pos (lam : ℝ) : 0 < 1 + lam ^ 2 / 3 := by positivity

/-- For `lam > 0`, the comparison `Fwin lam ≤ Hd lam` is equivalent to `0 ≤ Hwin lam`.

Indeed `Hwin lam = (6*lam - 3 - lam^2) / (3*lam)` and
`Hd lam - Fwin lam = (6*lam - 3 - lam^2) * (lam^2 - 3*lam + 3) / (6*lam*(3 + lam^2))`.
Since `lam > 0` and `lam^2 - 3*lam + 3 = (lam - 3/2)^2 + 3/4 > 0`, both quantities have the
sign of `6*lam - 3 - lam^2`. -/
theorem Hd_ge_Fwin_iff_of_pos {lam : ℝ} (hlam : 0 < lam) :
    Fwin lam ≤ Hd lam ↔ 0 ≤ Hwin lam := by
  have hden : (0:ℝ) < 1 + lam ^ 2 / 3 := one_add_sq_div_three_pos lam
  have hq : 0 < lam ^ 2 - 3 * lam + 3 := by nlinarith [sq_nonneg (lam - 3/2)]
  constructor
  · intro h
    have h' : Fwin lam * (1 + lam ^ 2 / 3) ≤ Hd lam * (1 + lam ^ 2 / 3) :=
      mul_le_mul_of_nonneg_right h hden.le
    rw [Fwin, div_mul_cancel₀ _ hden.ne'] at h'
    rw [Hd, Hwin] at h'
    rw [Hwin, ← sub_nonneg]
    have hkey : 0 ≤ (2 - 1 / lam - lam / 3) * (lam ^ 2 - 3 * lam + 3) := by
      have hlam' : lam ≠ 0 := ne_of_gt hlam
      field_simp at h' ⊢
      nlinarith [h', sq_nonneg lam, sq_nonneg (lam - 1)]
    nlinarith [hkey]
  · intro h
    rw [Fwin, Hd, Hwin, div_le_div_iff₀ hden (by norm_num : (0:ℝ) < 2)]
    rw [Hwin, ← sub_nonneg] at h
    have hlam' : lam ≠ 0 := ne_of_gt hlam
    have h3 : 0 ≤ 6 * lam - 3 - lam ^ 2 := by
      have := mul_nonneg h (by linarith : (0:ℝ) ≤ 3 * lam)
      field_simp at this ⊢
      nlinarith [this]
    have hkey : 0 ≤ (6 * lam - 3 - lam ^ 2) * (lam ^ 2 - 3 * lam + 3) := mul_nonneg h3 hq.le
    have hid : (1 + (2 - 1 / lam - lam / 3)) * (1 + lam ^ 2 / 3) - lam * 2
        = (6 * lam - 3 - lam ^ 2) * (lam ^ 2 - 3 * lam + 3) / (9 * lam) := by
      field_simp
      ring
    linarith [div_nonneg hkey (by linarith : (0:ℝ) ≤ 9 * lam), hid]

/-- **Target.** `H_d(λ) ≥ F(λ)` iff `H(λ) ≥ 0` on `0 < λ ≤ 1`.
(The hypothesis `lam ≤ 1` is stated as in the source, but is in fact not needed: see
`Hd_ge_Fwin_iff_of_pos`.) -/
theorem Hd_ge_Fwin_iff (lam : ℝ) (hlam : 0 < lam) (_hlam1 : lam ≤ 1) :
    Fwin lam ≤ Hd lam ↔ 0 ≤ Hwin lam :=
  Hd_ge_Fwin_iff_of_pos hlam

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

