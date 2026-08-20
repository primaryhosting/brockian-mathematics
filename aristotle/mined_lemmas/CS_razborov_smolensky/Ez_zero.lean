import Mathlib

/-!
# Binomial estimates

The estimates on binomial coefficients needed for the counting step of the
Razborov–Smolensky theorem.
-/

namespace CS

open Finset

/-- A quantitative form of `centralBinom m ≈ 4 ^ m / √(π m)`. -/

lemma Ez_zero : Ez q 0 = 0 := by
  have h : q - 1 ≠ 0 := by have := hq.out.two_le; omega
  simp [Ez, zero_pow h]

