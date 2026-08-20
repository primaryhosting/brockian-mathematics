import Mathlib

/-!
# Binomial estimates

The estimates on binomial coefficients needed for the counting step of the
Razborov–Smolensky theorem.
-/

namespace CS

open Finset

/-- A quantitative form of `centralBinom m ≈ 4 ^ m / √(π m)`. -/

lemma yv_apply {ζ : F} (i : Fin n) (x : Cube n) :
    yv F ζ i x = if x i then ζ else 1 := by
  by_cases h : x i <;> simp [yv, coord, h]

/-- `∏ i, y i` computes `ζ ^ (ones x)`. -/
