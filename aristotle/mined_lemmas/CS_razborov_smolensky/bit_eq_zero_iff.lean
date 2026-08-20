import Mathlib

/-!
# Binomial estimates

The estimates on binomial coefficients needed for the counting step of the
Razborov–Smolensky theorem.
-/

namespace CS

open Finset

/-- A quantitative form of `centralBinom m ≈ 4 ^ m / √(π m)`. -/

lemma bit_eq_zero_iff {b : Bool} : bit q b = 0 ↔ b = false := by
  cases b <;> simp [bit]

