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

def milnorConjecture : Prop :=
  ∀ n : ℕ, Nonempty (MilnorK2 F n ≃ₗ[ZMod 2] ContCoh.H (GalF F) n)

/-- The norm residue map in degree `0`: `k₀(F) = 𝔽₂ → H⁰(G_F, ℤ/2) = 𝔽₂`. -/
