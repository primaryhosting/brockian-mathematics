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
noncomputable def Hwin (lam : ℝ) : ℝ := 2 - 1 / lam - lam / 3

/-- `H_d(λ) = (1 + H(λ))/2`. -/
noncomputable def Hd (lam : ℝ) : ℝ := (1 + Hwin lam) / 2

/-- `F(λ) = λ / (1 + λ²/3)`. -/
noncomputable def Fwin (lam : ℝ) : ℝ := lam / (1 + lam ^ 2 / 3)

/-- Key algebraic identity behind the equivalence: after clearing the positive denominators
`2λ` and `1 + λ²/3`, the difference `H_d(λ) - F(λ)` has the sign of `-(λ² - 6λ + 3)`, since
`λ⁴ - 9λ³ + 24λ² - 27λ + 9 = (λ² - 6λ + 3)(λ² - 3λ + 3)` and the second factor is positive. -/
theorem quartic_factor (lam : ℝ) :
    lam ^ 4 - 9 * lam ^ 3 + 24 * lam ^ 2 - 27 * lam + 9
      = (lam ^ 2 - 6 * lam + 3) * (lam ^ 2 - 3 * lam + 3) := by
  ring

/-- `H_d(λ) ≥ F(λ)` iff `H(λ) ≥ 0`, for every `λ > 0`.

This is the unconditional form of the equivalence in eq. (1.3), third line, first equivalence:
the extra restriction `λ ≤ 1` is not needed. -/
theorem Hd_ge_Fwin_iff_of_pos (lam : ℝ) (hlam : 0 < lam) :
    Fwin lam ≤ Hd lam ↔ 0 ≤ Hwin lam := by
  have hd : (0:ℝ) < 1 + lam ^ 2 / 3 := by positivity
  have hq : (0:ℝ) < lam ^ 2 - 3 * lam + 3 := by nlinarith [sq_nonneg (2 * lam - 3)]
  have hinv : (1 / lam) * lam = 1 := by field_simp
  constructor
  · intro h
    have h' : Fwin lam * (1 + lam ^ 2 / 3) * (2 * lam) ≤ Hd lam * (1 + lam ^ 2 / 3) * (2 * lam) := by
      have := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right h hd.le) (by linarith : (0:ℝ) ≤ 2 * lam)
      simpa using this
    rw [Fwin, Hd, Hwin] at h'
    have e1 : lam / (1 + lam ^ 2 / 3) * (1 + lam ^ 2 / 3) = lam := by field_simp
    have e2 : (1 + (2 - 1 / lam - lam / 3)) / 2 * (1 + lam ^ 2 / 3) * (2 * lam)
        = (3 * lam - 1 - lam ^ 2 / 3) * (1 + lam ^ 2 / 3) := by
      field_simp; ring
    rw [e1, e2] at h'
    rw [Hwin]
    have hP : (lam ^ 2 - 6 * lam + 3) * (lam ^ 2 - 3 * lam + 3) ≤ 0 := by nlinarith [h']
    have key : lam ^ 2 - 6 * lam + 3 ≤ 0 := by nlinarith [hP, hq]
    nlinarith [key, hinv, hlam]
  · intro h
    rw [Hwin] at h
    have h1 : 1 / lam ≤ 2 - lam / 3 := by linarith
    have h2 : 1 ≤ (2 - lam / 3) * lam := by
      have := (div_le_iff₀ hlam).mp h1
      linarith
    have key : lam ^ 2 - 6 * lam + 3 ≤ 0 := by nlinarith
    rw [Fwin, Hd, Hwin, div_le_div_iff₀ hd (by norm_num : (0:ℝ) < 2)]
    nlinarith [mul_pos hlam hlam, sq_nonneg lam, hq, key, hinv]

/-- `H_d(λ) ≥ F(λ)` iff `H(λ) ≥ 0` on `0 < λ ≤ 1`
(preprint eq. (1.3), third line, first equivalence).

The hypothesis `λ ≤ 1` is part of the requested statement; the proof shows it is in fact
unnecessary, the equivalence holding for every `λ > 0` (see `Hd_ge_Fwin_iff_of_pos`). -/
theorem Hd_ge_Fwin_iff (lam : ℝ) (hlam : 0 < lam) (hlam1 : lam ≤ 1) :
    Fwin lam ≤ Hd lam ↔ 0 ≤ Hwin lam := by
  have _hlam1 := hlam1
  exact Hd_ge_Fwin_iff_of_pos lam hlam

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

