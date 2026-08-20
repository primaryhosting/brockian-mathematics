import Mathlib

/-!
# Binomial estimates

The estimates on binomial coefficients needed for the counting step of the
Razborov–Smolensky theorem.
-/

namespace CS

open Finset

/-- A quantitative form of `centralBinom m ≈ 4 ^ m / √(π m)`. -/

lemma yv_apply_mul_yinv_apply {ζ : F} (hζ : ζ ≠ 0) (i : Fin n) (x : Cube n) :
    yv F ζ i x * yinv F ζ i x = 1 := by
  by_cases h : x i <;> simp [yv, yinv, coord, h]
  field_simp

