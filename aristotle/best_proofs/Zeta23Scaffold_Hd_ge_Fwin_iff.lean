/-
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

/-- `H_d(λ) = (1 + H(λ))/2`. -/
noncomputable def Hd (lam : ℝ) : ℝ := (1 + Hwin lam) / 2

/-- `F(λ) = λ / (1 + λ²/3)`. -/
noncomputable def Fwin (lam : ℝ) : ℝ := lam / (1 + lam ^ 2 / 3)

/-- The quadratic `λ² - 3λ + 3` is strictly positive (its discriminant is `-3`). -/
lemma sq_sub_three_mul_add_three_pos (lam : ℝ) : 0 < lam ^ 2 - 3 * lam + 3 := by
  nlinarith [sq_nonneg (2 * lam - 3)]

/-- `1 + λ²/3 > 0`. -/
lemma one_add_sq_div_three_pos (lam : ℝ) : 0 < 1 + lam ^ 2 / 3 := by positivity

/-- Key algebraic identity: after clearing the positive denominators `6λ` and `3 + λ²`,
the difference `H_d(λ) - F(λ)` has numerator `(6λ - 3 - λ²)(λ² - 3λ + 3)`,
while `H(λ)` has numerator `6λ - 3 - λ²`. -/
lemma Hd_sub_Fwin_eq (lam : ℝ) (hlam : 0 < lam) :
    Hd lam - Fwin lam
      = ((6 * lam - 3 - lam ^ 2) * (lam ^ 2 - 3 * lam + 3))
          / (6 * lam * (3 + lam ^ 2)) := by
  have h1 : lam ≠ 0 := ne_of_gt hlam
  have h2 : (1 : ℝ) + lam ^ 2 / 3 ≠ 0 := ne_of_gt (one_add_sq_div_three_pos lam)
  have h3 : (3 : ℝ) + lam ^ 2 ≠ 0 := by positivity
  simp only [Hd, Fwin, Hwin]
  field_simp
  ring

/-- `H(λ) = (6λ - 3 - λ²) / (3λ)`. -/
lemma Hwin_eq (lam : ℝ) (hlam : 0 < lam) :
    Hwin lam = (6 * lam - 3 - lam ^ 2) / (3 * lam) := by
  have h1 : lam ≠ 0 := ne_of_gt hlam
  simp only [Hwin]
  field_simp
  ring

/-- Unconditional form (for all `λ > 0`): `F(λ) ≤ H_d(λ) ↔ 0 ≤ H(λ)`. -/
theorem Hd_ge_Fwin_iff_of_pos (lam : ℝ) (hlam : 0 < lam) :
    Fwin lam ≤ Hd lam ↔ 0 ≤ Hwin lam := by
  have hq : 0 < lam ^ 2 - 3 * lam + 3 := sq_sub_three_mul_add_three_pos lam
  have hden1 : 0 < 6 * lam * (3 + lam ^ 2) := by positivity
  have hden2 : 0 < 3 * lam := by positivity
  constructor
  · intro h
    have hd : 0 ≤ Hd lam - Fwin lam := by linarith
    rw [Hd_sub_Fwin_eq lam hlam, le_div_iff₀ hden1] at hd
    have hnum : 0 ≤ 6 * lam - 3 - lam ^ 2 := by nlinarith
    rw [Hwin_eq lam hlam]
    exact div_nonneg hnum hden2.le
  · intro h
    rw [Hwin_eq lam hlam] at h
    have hnum : 0 ≤ 6 * lam - 3 - lam ^ 2 := by
      by_contra hc
      push_neg at hc
      have : (6 * lam - 3 - lam ^ 2) / (3 * lam) < 0 := div_neg_of_neg_of_pos hc hden2
      linarith
    have hd : 0 ≤ Hd lam - Fwin lam := by
      rw [Hd_sub_Fwin_eq lam hlam]
      exact div_nonneg (mul_nonneg hnum hq.le) hden1.le
    linarith

/-- `H_d(λ) ≥ F(λ)` iff `H(λ) ≥ 0`, on `0 < λ ≤ 1` (preprint eq. (1.3), third line,
first equivalence).  The hypothesis `λ ≤ 1` is stated as in the source, but the proof
shows it is not needed: see `Hd_ge_Fwin_iff_of_pos`. -/
theorem Hd_ge_Fwin_iff :
    ∀ lam : ℝ, 0 < lam → lam ≤ 1 → (Fwin lam ≤ Hd lam ↔ 0 ≤ Hwin lam) :=
  fun lam hlam _ => Hd_ge_Fwin_iff_of_pos lam hlam

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

