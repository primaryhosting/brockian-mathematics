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

/-- For `a > 1` the base tent vanishes. -/
lemma T_eq_zero_of_one_lt {a : ℝ} (ha : 1 < a) : T a = 0 := by
  have h : |a| = a := abs_of_pos (lt_trans one_pos ha)
  simp only [T, h]
  exact max_eq_left (by linarith)

/-- On the band `(1, 5/2)`, the shifted tent `T (a - 3/2)` is strictly positive. -/
lemma T_shift_pos {a : ℝ} (h1 : 1 < a) (h2 : a < 5 / 2) : 0 < T (a - 3 / 2) := by
  have habs : |a - 3 / 2| < 1 := by
    rw [abs_lt]; constructor <;> linarith
  exact lt_max_of_lt_right (by linarith)

/-- The Fourier tent combination is strictly negative on the band `(1, 5/2)`. -/
theorem tent_combination_neg_on_band {a : ℝ} (h1 : 1 < a) (h2 : a < 5 / 2) :
    T a - (1 / 20) * (T (a - 3 / 2) + T (a + 3 / 2)) < 0 := by
  have hz : T a = 0 := T_eq_zero_of_one_lt h1
  have hp : 0 < T (a - 3 / 2) := T_shift_pos h1 h2
  have hn : 0 ≤ T (a + 3 / 2) := T_nonneg _
  rw [hz]
  linarith

end Zeta23Obstruction

