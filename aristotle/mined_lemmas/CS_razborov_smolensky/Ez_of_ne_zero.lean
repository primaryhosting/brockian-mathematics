import Mathlib

/-!
# Binomial estimates

The estimates on binomial coefficients needed for the counting step of the
Razborov–Smolensky theorem.
-/

namespace CS

open Finset

/-- A quantitative form of `centralBinom m ≈ 4 ^ m / √(π m)`. -/

lemma Ez_of_ne_zero {z : ZMod q} (h : z ≠ 0) : Ez q z = 1 := ZMod.pow_card_sub_one_eq_one h

