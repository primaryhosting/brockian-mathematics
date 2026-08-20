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

theorem neg_ne_self_of_ne_zero {x : Ksep F} (hx : x ≠ 0) : -x ≠ x := by
  intro h
  apply hx
  have h2 : (2 : Ksep F) * x = 0 := by linear_combination -h
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exact absurd h3 (NeZero.ne (2 : Ksep F))
  · exact h3

