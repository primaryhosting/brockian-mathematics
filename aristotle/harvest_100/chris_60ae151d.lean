/-
# Hwin Nonneg Iff Threshold
Category: A Assembly
Target: Zeta23Scaffold.Hwin_nonneg_iff_threshold
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Zeta23Scaffold

/-- The "window" function `H(λ) = 2 - 1/λ - λ/3`. -/
noncomputable def Hwin (lam : ℝ) : ℝ := 2 - 1 / lam - lam / 3

lemma sqrt_six_sq : (Real.sqrt 6) ^ 2 = 6 := Real.sq_sqrt (by norm_num)

lemma two_lt_sqrt_six : (2 : ℝ) < Real.sqrt 6 := by
  have h : Real.sqrt 4 < Real.sqrt 6 := by
    apply Real.sqrt_lt_sqrt <;> norm_num
  have h4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
  linarith [h4 ▸ h]

lemma sqrt_six_lt_three : Real.sqrt 6 < 3 := by
  have : Real.sqrt 6 < Real.sqrt 9 := by
    apply Real.sqrt_lt_sqrt <;> norm_num
  have h9 : Real.sqrt 9 = 3 := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 3)]
  linarith [h9 ▸ this]

/-- `H(λ) ≥ 0` iff `λ ≥ 3 - √6` on `0 < λ ≤ 1`. -/
theorem Hwin_nonneg_iff_threshold (lam : ℝ) (hpos : 0 < lam) (hle : lam ≤ 1) :
    0 ≤ Hwin lam ↔ 3 - Real.sqrt 6 ≤ lam := by
  have h6 : (Real.sqrt 6) ^ 2 = 6 := sqrt_six_sq
  have h2 : (2 : ℝ) < Real.sqrt 6 := two_lt_sqrt_six
  have h3 : Real.sqrt 6 < 3 := sqrt_six_lt_three
  have hne : lam ≠ 0 := ne_of_gt hpos
  have key : Hwin lam = (-(lam ^ 2) + 6 * lam - 3) / (3 * lam) := by
    simp only [Hwin]
    field_simp
    ring
  rw [key, le_div_iff₀ (by linarith : (0:ℝ) < 3 * lam)]
  constructor
  · intro h
    nlinarith [h6, h2, h3, sq_nonneg (lam - (3 - Real.sqrt 6))]
  · intro h
    nlinarith [h6, h2, h3, sq_nonneg (lam - (3 - Real.sqrt 6))]

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

