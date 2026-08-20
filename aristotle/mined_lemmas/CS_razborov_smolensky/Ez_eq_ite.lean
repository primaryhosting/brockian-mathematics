import Mathlib

/-!
# Binomial estimates

The estimates on binomial coefficients needed for the counting step of the
Razborov–Smolensky theorem.
-/

namespace CS

open Finset

/-- A quantitative form of `centralBinom m ≈ 4 ^ m / √(π m)`. -/

lemma Ez_eq_ite (z : ZMod q) : Ez q z = if z = 0 then 0 else 1 := by
  by_cases h : z = 0
  · simp [h, Ez_zero]
  · simp [h, Ez_of_ne_zero h]

/-- Half of the subsets of a set of field elements, not all zero, have nonzero sum. -/
