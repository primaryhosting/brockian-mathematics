/-!
# Hd Ge Fwin Iff
Category: A Assembly
Target: Zeta23Scaffold.Hd_ge_Fwin_iff
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Zeta23Scaffold

/-- The "window" function `H(λ) = 2 - 1/λ - λ/3`. -/
noncomputable def Hwin (lam : ℝ) : ℝ := 2 - 1 / lam - lam / 3

/-- `H_d(λ) = (1 + H(λ))/2`. -/
noncomputable def Hd (lam : ℝ) : ℝ := (1 + Hwin lam) / 2

/-- `F(λ) = λ / (1 + λ²/3)`. -/
noncomputable def Fwin (lam : ℝ) : ℝ := lam / (1 + lam ^ 2 / 3)

/-- The auxiliary quadratic `λ² - 3λ + 3` is strictly positive. -/
lemma aux_quadratic_pos (lam : ℝ) : 0 < lam ^ 2 - 3 * lam + 3 := by
  nlinarith [sq_nonneg (2 * lam - 3)]

/-- `0 ≤ H(λ)` is equivalent to the sign condition `0 ≤ 6λ - 3 - λ²` for `λ > 0`. -/
lemma Hwin_nonneg_iff {lam : ℝ} (hlam : 0 < lam) :
    0 ≤ Hwin lam ↔ 0 ≤ 6 * lam - 3 - lam ^ 2 := by
  rw [Hwin]
  rw [ge_iff_le, ← sub_nonneg]
  constructor
  · intro h
    have h' : 0 ≤ (2 - 1 / lam - lam / 3) * (3 * lam) := by positivity
    have : (2 - 1 / lam - lam / 3) * (3 * lam) = 6 * lam - 3 - lam ^ 2 := by
      field_simp; ring
    linarith [this ▸ h']
  · intro h
    have h3 : 0 < 3 * lam := by linarith
    have key : (2 - 1 / lam - lam / 3) * (3 * lam) = 6 * lam - 3 - lam ^ 2 := by
      field_simp; ring
    nlinarith [key, mul_pos h3 h3]

/-- The difference `H_d(λ) - F(λ)` factors as
`(6λ - 3 - λ²)(λ² - 3λ + 3) / (6λ(3 + λ²))`. -/
lemma Hd_sub_Fwin_eq {lam : ℝ} (hlam : 0 < lam) :
    Hd lam - Fwin lam =
      (6 * lam - 3 - lam ^ 2) * (lam ^ 2 - 3 * lam + 3) / (6 * lam * (3 + lam ^ 2)) := by
  have h1 : (1 : ℝ) + lam ^ 2 / 3 ≠ 0 := by positivity
  have h2 : lam ≠ 0 := ne_of_gt hlam
  have h3 : (3 : ℝ) + lam ^ 2 ≠ 0 := by positivity
  rw [Hd, Fwin, Hwin]
  field_simp
  ring

/-- `H_d(λ) ≥ F(λ)` iff `H(λ) ≥ 0`, for `0 < λ ≤ 1`. -/
theorem Hd_ge_Fwin_iff (lam : ℝ) (hpos : 0 < lam) (hle : lam ≤ 1) :
    Fwin lam ≤ Hd lam ↔ 0 ≤ Hwin lam := by
  have hden : 0 < 6 * lam * (3 + lam ^ 2) := by positivity
  have hq := aux_quadratic_pos lam
  rw [← sub_nonneg, Hd_sub_Fwin_eq hpos, Hwin_nonneg_iff hpos,
    div_nonneg_iff]
  constructor
  · rintro (⟨h, -⟩ | ⟨-, h⟩)
    · nlinarith
    · nlinarith
  · intro h
    exact Or.inl ⟨by nlinarith, le_of_lt hden⟩

end Zeta23Scaffold

