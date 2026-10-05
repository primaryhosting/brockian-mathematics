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

namespace Zeta23Obstruction

/-- The tent (triangular) profile `T a = max 0 (1 - |a|)`. -/
noncomputable def T : ℝ → ℝ := fun a => max 0 (1 - |a|)

/-- The tent profile is nonnegative. -/
lemma T_nonneg (a : ℝ) : 0 ≤ T a := le_max_left _ _

/-- The tent profile vanishes outside `[-1, 1]`. -/
lemma T_eq_zero_of_one_le_abs {a : ℝ} (h : 1 ≤ |a|) : T a = 0 := by
  simp only [T, max_eq_left_iff]
  linarith

/-- The tent profile is strictly positive on `(-1, 1)`. -/
lemma T_pos_of_abs_lt_one {a : ℝ} (h : |a| < 1) : 0 < T a := by
  have : (0 : ℝ) < 1 - |a| := by linarith
  exact lt_max_of_lt_right this

/-- On the band `(1, 5/2)`, the tent combination
`T α - (1/20) (T (α - 3/2) + T (α + 3/2))` is strictly negative. -/
theorem tent_combination_neg_on_band (a : ℝ) (h1 : 1 < a) (h2 : a < 5 / 2) :
    T a - (1 / 20) * (T (a - 3 / 2) + T (a + 3 / 2)) < 0 := by
  have ha : T a = 0 := by
    refine T_eq_zero_of_one_le_abs ?_
    rw [abs_of_pos (by linarith)]
    linarith
  have hshift : 0 < T (a - 3 / 2) := by
    refine T_pos_of_abs_lt_one ?_
    rw [abs_lt]
    constructor <;> linarith
  have hother : 0 ≤ T (a + 3 / 2) := T_nonneg _
  rw [ha]
  linarith

end Zeta23Obstruction

