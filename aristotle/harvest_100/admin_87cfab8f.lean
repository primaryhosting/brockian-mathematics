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

/-- For `lam > 0` the denominator `1 + lam^2/3` is positive. -/
lemma denom_pos (lam : ℝ) : (0 : ℝ) < 1 + lam ^ 2 / 3 := by
  nlinarith [sq_nonneg lam]

/-- `Hd lam - Fwin lam` has, for `lam > 0`, the sign of `6*lam - 3 - lam^2`,
since `6*lam*(3 + lam^2)*(Hd lam - Fwin lam) = (6*lam - 3 - lam^2)*(lam^2 - 3*lam + 3)`
and `lam^2 - 3*lam + 3 > 0`. -/
lemma key_identity {lam : ℝ} (hlam : 0 < lam) :
    6 * lam * (3 + lam ^ 2) * (Hd lam - Fwin lam)
      = (6 * lam - 3 - lam ^ 2) * (lam ^ 2 - 3 * lam + 3) := by
  have h1 : lam ≠ 0 := ne_of_gt hlam
  have h2 : (1 : ℝ) + lam ^ 2 / 3 ≠ 0 := ne_of_gt (denom_pos lam)
  simp only [Hd, Hwin, Fwin]
  field_simp
  ring

/-- The equivalence `F(λ) ≤ H_d(λ) ↔ 0 ≤ H(λ)`, valid for every `λ > 0`. -/
theorem Hd_ge_Fwin_iff_of_pos (lam : ℝ) (hlam : 0 < lam) :
    Fwin lam ≤ Hd lam ↔ 0 ≤ Hwin lam := by
  have hq : (0 : ℝ) < lam ^ 2 - 3 * lam + 3 := by nlinarith [sq_nonneg (2 * lam - 3)]
  have hc : (0 : ℝ) < 6 * lam * (3 + lam ^ 2) := by nlinarith [sq_nonneg lam]
  have hkey := key_identity hlam
  have hHid : 3 * lam * Hwin lam = 6 * lam - 3 - lam ^ 2 := by
    simp only [Hwin]
    field_simp
    ring
  have h3l : (0 : ℝ) < 3 * lam := by linarith
  have hH : 0 ≤ Hwin lam ↔ 0 ≤ 6 * lam - 3 - lam ^ 2 := by
    constructor
    · intro h; nlinarith [mul_nonneg h3l.le h]
    · intro h
      by_contra hneg
      push_neg at hneg
      nlinarith [mul_pos h3l (neg_pos.mpr hneg)]
  rw [hH, ← sub_nonneg]
  constructor
  · intro h
    nlinarith [mul_nonneg hc.le h]
  · intro h
    nlinarith [mul_nonneg h hq.le]

/-- `H_d(λ) ≥ F(λ)` iff `H(λ) ≥ 0` on `0 < λ ≤ 1` (preprint eq. (1.3), third line,
first equivalence).  The hypothesis `lam ≤ 1` is part of the requested statement but is
not needed: see `Hd_ge_Fwin_iff_of_pos`, which holds for all `lam > 0`. -/
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

