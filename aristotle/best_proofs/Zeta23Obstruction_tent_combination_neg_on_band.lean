/-
# Tent Combination Neg On Band
Category: Brockian Corpus
Target: Zeta23Obstruction.tent_combination_neg_on_band
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Zeta23Obstruction

/-- The Fourier tent profile `T(a) = max 0 (1 - |a|)`. -/
noncomputable def T : ℝ → ℝ := fun a => max 0 (1 - |a|)

/-- The tent is nonnegative everywhere. -/
lemma T_nonneg (a : ℝ) : 0 ≤ T a := le_max_left _ _

/-- For `1 ≤ a`, the tent vanishes. -/
lemma T_eq_zero_of_one_le {a : ℝ} (ha : 1 ≤ a) : T a = 0 := by
  have : |a| = a := abs_of_nonneg (le_trans zero_le_one ha)
  simp [T, this]
  linarith

/-- On `(1, 5/2)` the shifted tent is strictly positive. -/
lemma T_shift_pos {a : ℝ} (h1 : 1 < a) (h2 : a < 5 / 2) : 0 < T (a - 3 / 2) := by
  have habs : |a - 3 / 2| < 1 := by
    rw [abs_lt]; constructor <;> linarith
  have : 0 < 1 - |a - 3 / 2| := by linarith
  exact lt_of_lt_of_le this (le_max_right _ _)

/--
The witness's Fourier tent combination is strictly negative on the band `(1, 5/2)`:
`T a - (1/20) * (T (a - 3/2) + T (a + 3/2)) < 0`.
-/
theorem tent_combination_neg_on_band {a : ℝ} (h1 : 1 < a) (h2 : a < 5 / 2) :
    T a - (1 / 20) * (T (a - 3 / 2) + T (a + 3 / 2)) < 0 := by
  have hz : T a = 0 := T_eq_zero_of_one_le h1.le
  have hp : 0 < T (a - 3 / 2) := T_shift_pos h1 h2
  have hq : 0 ≤ T (a + 3 / 2) := T_nonneg _
  rw [hz]
  linarith

end Zeta23Obstruction

