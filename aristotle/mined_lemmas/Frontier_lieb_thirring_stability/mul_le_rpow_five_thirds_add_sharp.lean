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

lemma mul_le_rpow_five_thirds_add_sharp {Kc t : ℝ} (hKc : 0 < Kc) (ht : 0 ≤ t) :
    ∃ a : ℝ, 0 ≤ a ∧ t * a = Kc * a ^ (5 / 3 : ℝ) + ltConst Kc * t ^ (5 / 2 : ℝ) := by
  refine ⟨(3 * t / (5 * Kc)) ^ (3 / 2 : ℝ), Real.rpow_nonneg (by positivity) _, ?_⟩
  rcases eq_or_lt_of_le ht with h | ht'
  · rw [← h]
    norm_num
  set s : ℝ := 3 * t / (5 * Kc) with hs
  have hspos : 0 < s := by rw [hs]; positivity
  have hts : t = (5 * Kc / 3) * s := by rw [hs]; field_simp
  have e1 : (s ^ (3 / 2 : ℝ)) ^ (5 / 3 : ℝ) = s ^ (5 / 2 : ℝ) := by
    rw [← Real.rpow_mul hspos.le]; norm_num
  have e2 : s ^ (5 / 2 : ℝ) = s ^ (3 / 2 : ℝ) * s := by
    rw [show (5 / 2 : ℝ) = 3 / 2 + 1 by norm_num, Real.rpow_add hspos, Real.rpow_one]
  have e3 : t ^ (5 / 2 : ℝ) = (5 * Kc / 3) ^ (5 / 2 : ℝ) * s ^ (5 / 2 : ℝ) := by
    rw [hts]; exact Real.mul_rpow (by positivity) hspos.le
  have e4 : (2 / 5 : ℝ) * (3 / (5 * Kc)) ^ (3 / 2 : ℝ) * (5 * Kc / 3) ^ (5 / 2 : ℝ)
      = (2 / 5) * (5 * Kc / 3) := by
    have h : (3 / (5 * Kc) : ℝ) = ((5 * Kc / 3))⁻¹ := by field_simp
    rw [h, Real.inv_rpow (by positivity)]
    rw [show (5 / 2 : ℝ) = 3 / 2 + 1 by norm_num, Real.rpow_add (by positivity), Real.rpow_one]
    field_simp
  rw [ltConst, e1, e3, e2]
  linear_combination (s ^ (3 / 2 : ℝ)) * hts - (s ^ (3 / 2 : ℝ) * s) * e4

/-! ## Abstract energy lower bound on a measure space -/

/-- Lieb–Thirring type kinetic energy bound: the kinetic energy `T` dominates
`Kc * ∫ ρ ^ (5/3)`. -/
