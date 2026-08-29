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

/-- The quadratic `λ² - 3λ + 3` is strictly positive. -/
lemma quad_pos (lam : ℝ) : 0 < lam ^ 2 - 3 * lam + 3 := by
  nlinarith [sq_nonneg (2 * lam - 3)]

/-- `H_d(λ) ≥ F(λ)` iff `H(λ) ≥ 0`, for `0 < λ ≤ 1` (preprint eq. (1.3)). -/
theorem Hd_ge_Fwin_iff (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) :
    Fwin lam ≤ Hd lam ↔ 0 ≤ Hwin lam := by
  have hden : (0 : ℝ) < 1 + lam ^ 2 / 3 := by positivity
  have hq := quad_pos lam
  have hkey : Hd lam - Fwin lam =
      (Hwin lam * (lam ^ 2 - 3 * lam + 3)) / (2 * (1 + lam ^ 2 / 3)) := by
    unfold Hd Fwin Hwin
    field_simp
    ring
  constructor
  · intro h
    have hd : 0 ≤ Hd lam - Fwin lam := by linarith
    rw [hkey] at hd
    have h2 : (0 : ℝ) < 2 * (1 + lam ^ 2 / 3) := by linarith
    have := (div_nonneg_iff.mp hd)
    rcases this with ⟨hnum, _⟩ | ⟨_, hneg⟩
    · exact nonneg_of_mul_nonneg_right hnum hq
    · linarith
  · intro h
    have h2 : (0 : ℝ) < 2 * (1 + lam ^ 2 / 3) := by linarith
    have : 0 ≤ Hd lam - Fwin lam := by
      rw [hkey]
      exact div_nonneg (mul_nonneg h hq.le) h2.le
    linarith

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

