import Mathlib

/-!
# Mod-2 Milnor K-theory of a field

For a field `F` we define
`k_n(F) = K^M_n(F)/2`, the `n`-th mod-2 Milnor K-group, as the quotient of the `n`-fold
tensor power over `𝔽₂` of the square class group `F^×/(F^×)²` by the Steinberg relations
`{a, 1-a} = 0`.
-/

open scoped TensorProduct

namespace MilnorK

variable (F : Type) [Field F]

/-- The subgroup of squares of `Fˣ`. -/

theorem sqrtOf_ne_zero (a : Fˣ) : sqrtOf F (a : F) ≠ 0 := by
  intro h
  have hh := sqrtOf_mul_self F (a : F)
  rw [h, mul_zero] at hh
  exact a.ne_zero ((map_eq_zero (algebraMap F (Ksep F))).1 hh.symm)

