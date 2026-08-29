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

/-- The unit tent profile `T a = max 0 (1 - |a|)`. -/
noncomputable def T : ℝ → ℝ := fun a => max 0 (1 - |a|)

/-- The tent profile is nonnegative. -/
lemma T_nonneg (a : ℝ) : 0 ≤ T a := le_max_left _ _

/-- Outside the unit interval the tent vanishes. -/
lemma T_eq_zero_of_one_le_abs {a : ℝ} (ha : 1 ≤ |a|) : T a = 0 := by
  simp [T, sub_nonpos.mpr ha]

/-- Inside the unit interval the tent is strictly positive. -/
lemma T_pos_of_abs_lt_one {a : ℝ} (ha : |a| < 1) : 0 < T a := by
  have : 0 < 1 - |a| := by linarith
  exact lt_max_of_lt_right this

/--
The Fourier tent combination `T α - (1/20)(T (α - 3/2) + T (α + 3/2))` is strictly
negative on the band `1 < α < 5/2`.
-/
theorem tent_combination_neg_on_band {a : ℝ} (h1 : 1 < a) (h2 : a < 5 / 2) :
    T a - (1 / 20) * (T (a - 3 / 2) + T (a + 3 / 2)) < 0 := by
  have habs : |a| = a := abs_of_pos (by linarith)
  have hTa : T a = 0 := T_eq_zero_of_one_le_abs (by rw [habs]; linarith)
  have hshift : |a - 3 / 2| < 1 := by
    rw [abs_lt]; constructor <;> linarith
  have hpos : 0 < T (a - 3 / 2) := T_pos_of_abs_lt_one hshift
  have hnn : 0 ≤ T (a + 3 / 2) := T_nonneg _
  rw [hTa]
  linarith

end Zeta23Obstruction

