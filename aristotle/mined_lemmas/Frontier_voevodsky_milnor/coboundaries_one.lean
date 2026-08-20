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

theorem coboundaries_one : coboundaries G 1 = ⊥ := by
  refine le_antisymm ?_ bot_le
  rintro _ ⟨f, -, rfl⟩
  simpa using d_zero_eq_zero f

/-- Degree-`0` cocycles are just the constants. -/
