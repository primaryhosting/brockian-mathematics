import Mathlib

/-!
# Tent Combination Neg On Band
Category: Brockian Corpus
Target: Zeta23Obstruction.tent_combination_neg_on_band
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

namespace Zeta23Obstruction

/-- The tent profile `T a = max 0 (1 - |a|)`. -/
noncomputable def T : ℝ → ℝ := fun a => max 0 (1 - |a|)

/-- `T` is nonnegative. -/
lemma T_nonneg (a : ℝ) : 0 ≤ T a := le_max_left _ _

/-- For `1 < a`, the base tent vanishes. -/
lemma T_eq_zero_of_one_lt {a : ℝ} (ha : 1 < a) : T a = 0 := by
  have h : |a| = a := abs_of_pos (lt_trans zero_lt_one ha)
  simp only [T, h]
  exact max_eq_left (by linarith)

/-- For `|a| < 1`, the tent is strictly positive. -/
lemma T_pos_of_abs_lt_one {a : ℝ} (ha : |a| < 1) : 0 < T a :=
  lt_max_of_lt_right (by linarith)

/-- The Fourier tent combination is strictly negative on the band `(1, 5/2)`. -/
theorem tent_combination_neg_on_band {a : ℝ} (h1 : 1 < a) (h2 : a < 5 / 2) :
    T a - (1 / 20) * (T (a - 3 / 2) + T (a + 3 / 2)) < 0 := by
  have hz : T a = 0 := T_eq_zero_of_one_lt h1
  have habs : |a - 3 / 2| < 1 := by
    rw [abs_lt]; constructor <;> linarith
  have hpos : 0 < T (a - 3 / 2) := T_pos_of_abs_lt_one habs
  have hnn : 0 ≤ T (a + 3 / 2) := T_nonneg _
  rw [hz]
  linarith

end Zeta23Obstruction

