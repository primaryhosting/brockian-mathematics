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

noncomputable def milnorK2ZeroEquiv : MilnorK2 F 0 ≃ₗ[ZMod 2] ZMod 2 :=
  (Submodule.quotEquivOfEqBot _ (steinberg_eq_bot_of_lt_two F (by norm_num))).trans
    (PiTensorProduct.isEmptyEquiv (Fin 0))

/-- `k_1(F) ≅ F^×/(F^×)²`. -/
