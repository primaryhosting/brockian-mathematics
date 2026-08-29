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

/-- Key algebraic identity: for `λ > 0`,
`6λ(3 + λ²) · (H_d(λ) - F(λ)) = (6λ - 3 - λ²) · (λ² - 3λ + 3)`,
and `3λ · H(λ) = 6λ - 3 - λ²`. -/
theorem Hd_sub_Fwin_mul (lam : ℝ) (hlam : 0 < lam) :
    (6 * lam * (3 + lam ^ 2)) * (Hd lam - Fwin lam)
      = (6 * lam - 3 - lam ^ 2) * (lam ^ 2 - 3 * lam + 3) := by
  have h1 : lam ≠ 0 := ne_of_gt hlam
  have h2 : (1 : ℝ) + lam ^ 2 / 3 ≠ 0 := by positivity
  simp only [Hd, Fwin, Hwin]
  field_simp
  ring

/-- `H_d(λ) ≥ F(λ)` if and only if `H(λ) ≥ 0`, for `0 < λ ≤ 1`
(preprint eq. (1.3), third line, first equivalence).

The hypothesis `lam ≤ 1` is included as stated in the target, but it turns out to be
unnecessary: the equivalence holds for every `λ > 0`. -/
theorem Hd_ge_Fwin_iff (lam : ℝ) (hlam : 0 < lam) (hlam1 : lam ≤ 1) :
    Fwin lam ≤ Hd lam ↔ 0 ≤ Hwin lam := by
  clear hlam1
  have hpos : 0 < 6 * lam * (3 + lam ^ 2) := by positivity
  have hq : 0 < lam ^ 2 - 3 * lam + 3 := by nlinarith [sq_nonneg (2 * lam - 3)]
  have hH : 3 * lam * Hwin lam = 6 * lam - 3 - lam ^ 2 := by
    simp only [Hwin]
    field_simp
    ring
  have hkey := Hd_sub_Fwin_mul lam hlam
  constructor
  · intro h
    have h1 : 0 ≤ (6 * lam - 3 - lam ^ 2) * (lam ^ 2 - 3 * lam + 3) := by
      rw [← hkey]
      have : 0 ≤ Hd lam - Fwin lam := by linarith
      positivity
    have h2 : 0 ≤ 6 * lam - 3 - lam ^ 2 := by nlinarith [h1, hq]
    nlinarith [hH]
  · intro h
    have h2 : 0 ≤ 6 * lam - 3 - lam ^ 2 := by nlinarith
    have h1 : 0 ≤ (6 * lam * (3 + lam ^ 2)) * (Hd lam - Fwin lam) := by
      rw [hkey]; positivity
    nlinarith [h1]

end Zeta23Scaffold

