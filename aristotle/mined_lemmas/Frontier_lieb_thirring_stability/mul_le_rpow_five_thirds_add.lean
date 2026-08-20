/-
# Lieb Thirring Stability
Category: Frontier Physics
Target: Frontier.lieb_thirring_stability
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Lieb Thirring Stability
Category: Frontier Physics
Target: Frontier.lieb_thirring_stability
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

namespace Frontier

open MeasureTheory

/-! ## The pointwise (Young) inequality underlying stability -/

/-- The Lieb–Thirring stability constant appearing in the bound
`Kc * a ^ (5/3) - t * a ≥ - ltConst Kc * t ^ (5/2)`. -/

lemma mul_le_rpow_five_thirds_add {Kc t a : ℝ} (hKc : 0 < Kc) (ht : 0 ≤ t) (ha : 0 ≤ a) :
    t * a ≤ Kc * a ^ (5 / 3 : ℝ) + ltConst Kc * t ^ (5 / 2 : ℝ) := by
  have hconj : Real.HolderConjugate (5 / 3 : ℝ) (5 / 2) := by constructor <;> norm_num
  set lam : ℝ := (5 * Kc / 3) ^ (3 / 5 : ℝ) with hlam
  have hlampos : 0 < lam := Real.rpow_pos_of_pos (by linarith) _
  have h := Real.young_inequality_of_nonneg (a := lam * a) (b := t / lam)
    (by positivity) (by positivity) hconj
  have hmul : (lam * a) * (t / lam) = t * a := by field_simp
  rw [hmul] at h
  refine h.trans_eq ?_
  have h1 : (lam * a) ^ (5 / 3 : ℝ) = lam ^ (5 / 3 : ℝ) * a ^ (5 / 3 : ℝ) :=
    Real.mul_rpow hlampos.le ha
  have h2 : lam ^ (5 / 3 : ℝ) = 5 * Kc / 3 := by
    rw [hlam, ← Real.rpow_mul (by linarith)]
    norm_num
  have h3 : (t / lam) ^ (5 / 2 : ℝ) = t ^ (5 / 2 : ℝ) / lam ^ (5 / 2 : ℝ) :=
    Real.div_rpow ht hlampos.le _
  have h4 : lam ^ (5 / 2 : ℝ) = (5 * Kc / 3) ^ (3 / 2 : ℝ) := by
    rw [hlam, ← Real.rpow_mul (by linarith)]
    norm_num
  have h5 : (3 / (5 * Kc)) ^ (3 / 2 : ℝ) = ((5 * Kc / 3) ^ (3 / 2 : ℝ))⁻¹ := by
    rw [show (3 : ℝ) / (5 * Kc) = (5 * Kc / 3)⁻¹ by field_simp, Real.inv_rpow (by positivity)]
  have h6 : (0 : ℝ) < (5 * Kc / 3) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
  rw [ltConst, h1, h2, h3, h4, h5]
  field_simp

/-- **Sharpness**: equality holds in `mul_le_rpow_five_thirds_add` at `a = (3t/(5Kc))^{3/2}`,
so `ltConst Kc` is the optimal constant in that pointwise bound. -/
