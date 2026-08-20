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

noncomputable def H0Equiv : H G 0 ≃ₗ[ZMod 2] ZMod 2 :=
  (Submodule.quotEquivOfEqBot _ (by rw [coboundaries_zero]; simp)).trans (cocyclesZeroEquiv G)

/-- The subgroup of continuous homomorphisms `G → ZMod 2`, i.e. continuous `1`-cocycles. -/
