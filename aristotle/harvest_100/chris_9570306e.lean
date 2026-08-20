import Mathlib

/-!
# Hd Ge Fwin Iff
Category: A Assembly
Target: Zeta23Scaffold.Hd_ge_Fwin_iff
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Zeta23Scaffold

/-- The "window" function `H(λ) = 2 - 1/λ - λ/3`. -/
noncomputable def Hwin (lam : ℝ) : ℝ := 2 - 1 / lam - lam / 3

/-- `H_d(λ) = (1 + H(λ))/2`. -/
noncomputable def Hd (lam : ℝ) : ℝ := (1 + Hwin lam) / 2

/-- `F(λ) = λ / (1 + λ²/3)`. -/
noncomputable def Fwin (lam : ℝ) : ℝ := lam / (1 + lam ^ 2 / 3)

/-- Key algebraic identity: after clearing the positive denominators, the difference
`H_d(λ) - F(λ)` has numerator `(6λ - 3 - λ²) * (λ² - 3λ + 3)`, while `H(λ)` has
numerator `6λ - 3 - λ²`; since `λ² - 3λ + 3 > 0`, the two signs agree. -/
theorem Hd_sub_Fwin_eq (lam : ℝ) (hlam : 0 < lam) :
    Hd lam - Fwin lam
      = (6 * lam - 3 - lam ^ 2) * (lam ^ 2 - 3 * lam + 3) / (6 * lam * (3 + lam ^ 2)) := by
  have h1 : lam ≠ 0 := ne_of_gt hlam
  have h2 : (3 : ℝ) + lam ^ 2 > 0 := by positivity
  have h3 : (1 : ℝ) + lam ^ 2 / 3 ≠ 0 := by positivity
  unfold Hd Fwin Hwin
  field_simp
  ring

/-- `H(λ)` has the same sign as `6λ - 3 - λ²` (for `λ > 0`). -/
theorem Hwin_nonneg_iff (lam : ℝ) (hlam : 0 < lam) :
    0 ≤ Hwin lam ↔ 0 ≤ 6 * lam - 3 - lam ^ 2 := by
  have h1 : lam ≠ 0 := ne_of_gt hlam
  have : Hwin lam = (6 * lam - 3 - lam ^ 2) / (3 * lam) := by
    unfold Hwin; field_simp; ring
  rw [this, le_div_iff₀ (by positivity)]
  constructor <;> intro h <;> nlinarith

/-- Unconditional form (valid for all `λ > 0`): `F(λ) ≤ H_d(λ) ↔ 0 ≤ H(λ)`. -/
theorem Hd_ge_Fwin_iff_of_pos (lam : ℝ) (hlam : 0 < lam) :
    Fwin lam ≤ Hd lam ↔ 0 ≤ Hwin lam := by
  have hq : (0 : ℝ) < lam ^ 2 - 3 * lam + 3 := by nlinarith [sq_nonneg (2 * lam - 3)]
  have hden : (0 : ℝ) < 6 * lam * (3 + lam ^ 2) := by positivity
  rw [← sub_nonneg, Hd_sub_Fwin_eq lam hlam, le_div_iff₀ hden, Hwin_nonneg_iff lam hlam]
  constructor <;> intro h <;> nlinarith

/-- `H_d(λ) ≥ F(λ)` iff `H(λ) ≥ 0` on `0 < λ ≤ 1` (preprint eq. (1.3), third line,
first equivalence).  The hypothesis `λ ≤ 1` was requested in the statement, but the
equivalence in fact holds for every `λ > 0` (see `Hd_ge_Fwin_iff_of_pos`). -/
theorem Hd_ge_Fwin_iff (lam : ℝ) (hlam : 0 < lam) (hlam1 : lam ≤ 1) :
    Fwin lam ≤ Hd lam ↔ 0 ≤ Hwin lam := by
  have _hle : lam ≤ 1 := hlam1
  exact Hd_ge_Fwin_iff_of_pos lam hlam

end Zeta23Scaffold

