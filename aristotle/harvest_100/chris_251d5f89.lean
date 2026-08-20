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

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Zeta23Obstruction

/-- The unit tent function `T a = max 0 (1 - |a|)`. -/
noncomputable def T : ℝ → ℝ := fun a => max 0 (1 - |a|)

/-- On the band `(1, 5/2)`, the tent combination
`T a - (1/20) * (T (a - 3/2) + T (a + 3/2))` is strictly negative. -/
theorem tent_combination_neg_on_band (a : ℝ) (h1 : 1 < a) (h2 : a < 5 / 2) :
    T a - (1 / 20) * (T (a - 3 / 2) + T (a + 3 / 2)) < 0 := by
  have habs : |a| = a := abs_of_pos (by linarith)
  have hTa : T a = 0 := by
    simp only [T, habs]
    exact max_eq_left (by linarith)
  have hshift : 0 < T (a - 3 / 2) := by
    have : |a - 3 / 2| < 1 := by
      rw [abs_lt]; constructor <;> linarith
    simp only [T]
    exact lt_max_of_lt_right (by linarith)
  have hplus : 0 ≤ T (a + 3 / 2) := le_max_left _ _
  rw [hTa]
  linarith

end Zeta23Obstruction

