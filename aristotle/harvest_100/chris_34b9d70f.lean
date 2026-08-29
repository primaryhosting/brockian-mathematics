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

/-- For `0 < lam ≤ 1` we have `Fwin lam ≤ Hd lam` iff `0 ≤ Hwin lam`
(preprint eq. (1.3), third line, first equivalence).

The key algebraic identity is
`Hd lam - Fwin lam = (6*lam - 3 - lam^2) * (lam^2 - 3*lam + 3) / (6*lam*(3 + lam^2))`,
where the second factor of the numerator and the denominator are positive,
while `Hwin lam = (6*lam - 3 - lam^2)/(3*lam)`.

The hypothesis `lam ≤ 1` is kept because it is part of the requested statement, but it turns
out to be unnecessary: the equivalence holds for every `lam > 0`. -/
theorem Hd_ge_Fwin_iff (lam : ℝ) (hlam : 0 < lam) (hlam1 : lam ≤ 1) :
    Fwin lam ≤ Hd lam ↔ 0 ≤ Hwin lam := by
  have hlam' : lam ≠ 0 := ne_of_gt hlam
  have hden : (0 : ℝ) < 3 + lam ^ 2 := by positivity
  have hq : (0 : ℝ) < lam ^ 2 - 3 * lam + 3 := by nlinarith [sq_nonneg (2 * lam - 3)]
  have hD : (0 : ℝ) < 6 * lam * (3 + lam ^ 2) := by positivity
  have hD3 : (0 : ℝ) < 3 * lam := by positivity
  have key : Hd lam - Fwin lam
      = (6 * lam - 3 - lam ^ 2) * (lam ^ 2 - 3 * lam + 3) / (6 * lam * (3 + lam ^ 2)) := by
    unfold Hd Fwin Hwin
    field_simp
    ring
  have key2 : Hwin lam = (6 * lam - 3 - lam ^ 2) / (3 * lam) := by
    unfold Hwin
    field_simp
    ring
  rw [← sub_nonneg, key, key2, le_div_iff₀ hD, le_div_iff₀ hD3]
  constructor
  · intro h
    nlinarith
  · intro h
    nlinarith

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

