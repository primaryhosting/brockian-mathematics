/-
# Tent Combination Neg On Band
Category: Brockian Corpus
Target: Zeta23Obstruction.tent_combination_neg_on_band
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Tent Combination Neg On Band
Category: Brockian Corpus
Target: Zeta23Obstruction.tent_combination_neg_on_band
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Zeta23Obstruction

/-- The tent (triangular) profile `T a = max 0 (1 - |a|)`. -/
noncomputable def T : ℝ → ℝ := fun a => max 0 (1 - |a|)

/-- On the band `(1, 5/2)`, the combination `T a - (1/20)(T (a - 3/2) + T (a + 3/2))`
is strictly negative. -/
theorem tent_combination_neg_on_band (a : ℝ) (h1 : 1 < a) (h2 : a < 5 / 2) :
    T a - (1 / 20) * (T (a - 3 / 2) + T (a + 3 / 2)) < 0 := by
  have habs : |a| = a := abs_of_pos (by linarith)
  have hT0 : T a = 0 := by
    simp [T, habs]
    linarith
  have hshift : |a - 3 / 2| < 1 := by
    rw [abs_lt]; constructor <;> linarith
  have hTs : T (a - 3 / 2) = 1 - |a - 3 / 2| := by
    have : (0:ℝ) ≤ 1 - |a - 3/2| := by linarith
    simp [T, max_eq_right this]
  have hTs_pos : 0 < T (a - 3 / 2) := by rw [hTs]; linarith
  have hTp : 0 ≤ T (a + 3 / 2) := le_max_left _ _
  rw [hT0]
  linarith

end Zeta23Obstruction

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

