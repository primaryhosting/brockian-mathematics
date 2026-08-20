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

theorem eq_or_eq_neg_of_mul_self_eq {r s : Ksep F} (h : r * r = s * s) : s = r ∨ s = -r := by
  have h0 : (s - r) * (s + r) = 0 := by linear_combination -h
  rcases mul_eq_zero.1 h0 with h' | h'
  · exact Or.inl (by linear_combination h')
  · exact Or.inr (by linear_combination h')

/-- Any automorphism sends a square root of an element of `F` to `± ` itself. -/
