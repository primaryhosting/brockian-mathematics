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

/-- Key algebraic identity: for `lam > 0`,
`Hd lam - Fwin lam = (6*lam - 3 - lam^2) * (lam^2 - 3*lam + 3) / (6*lam*(3 + lam^2))`. -/
theorem Hd_sub_Fwin_eq (lam : ℝ) (hlam : 0 < lam) :
    Hd lam - Fwin lam =
      (6 * lam - 3 - lam ^ 2) * (lam ^ 2 - 3 * lam + 3) / (6 * lam * (3 + lam ^ 2)) := by
  have h1 : (1 : ℝ) + lam ^ 2 / 3 ≠ 0 := by positivity
  have h2 : (3 : ℝ) + lam ^ 2 ≠ 0 := by positivity
  unfold Hd Fwin Hwin
  field_simp
  ring

/-- `0 ≤ Hwin lam` is equivalent to the sign condition `0 ≤ 6*lam - 3 - lam^2`, for `lam > 0`. -/
theorem Hwin_nonneg_iff (lam : ℝ) (hlam : 0 < lam) :
    0 ≤ Hwin lam ↔ 0 ≤ 6 * lam - 3 - lam ^ 2 := by
  have hkey : Hwin lam = (6 * lam - 3 - lam ^ 2) / (3 * lam) := by
    unfold Hwin
    field_simp
    ring
  rw [hkey, le_div_iff₀ (by positivity : (0:ℝ) < 3 * lam), zero_mul]

/-- Unconditional form (only positivity of `lam` is needed):
`Fwin lam ≤ Hd lam ↔ 0 ≤ Hwin lam`. -/
theorem Hd_ge_Fwin_iff_of_pos (lam : ℝ) (hlam : 0 < lam) :
    Fwin lam ≤ Hd lam ↔ 0 ≤ Hwin lam := by
  have hq : 0 < lam ^ 2 - 3 * lam + 3 := by nlinarith [sq_nonneg (2 * lam - 3)]
  have hden : 0 < 6 * lam * (3 + lam ^ 2) := by positivity
  rw [← sub_nonneg, Hd_sub_Fwin_eq lam hlam, Hwin_nonneg_iff lam hlam,
    le_div_iff₀ hden]
  constructor
  · intro h
    nlinarith [h, hq]
  · intro h
    nlinarith [h, hq]

/-- `H_d(λ) ≥ F(λ)` iff `H(λ) ≥ 0` on `0 < λ ≤ 1` (preprint eq. (1.3), third line,
first equivalence).  The hypothesis `lam ≤ 1` is not needed for the argument, but is
kept here as it appears in the source statement; see `Hd_ge_Fwin_iff_of_pos` for the
version assuming only `0 < lam`. -/
theorem Hd_ge_Fwin_iff (lam : ℝ) (hlam : 0 < lam) (_hlam1 : lam ≤ 1) :
    Fwin lam ≤ Hd lam ↔ 0 ≤ Hwin lam :=
  Hd_ge_Fwin_iff_of_pos lam hlam

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

