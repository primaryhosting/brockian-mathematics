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

def sqUnits : Subgroup Fˣ where
  carrier := {x | ∃ y : Fˣ, y ^ 2 = x}
  one_mem' := ⟨1, one_pow 2⟩
  mul_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a * b, by rw [mul_pow]⟩
  inv_mem' := by
    rintro _ ⟨a, rfl⟩
    exact ⟨a⁻¹, by rw [inv_pow]⟩

/-- The group of square classes `F^× / (F^×)²`, written additively. This is `k_1(F)`. -/
