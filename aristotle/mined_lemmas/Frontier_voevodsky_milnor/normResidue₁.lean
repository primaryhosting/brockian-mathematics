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

noncomputable def normResidue₁ : MilnorK2 F 1 →ₗ[ZMod 2] ContCoh.H (GalF F) 1 :=
  (ContCoh.H1Equiv (GalF F)).symm.toLinearMap ∘ₗ
    (Kummer.kummerMap F ∘ₗ (milnorK2OneEquiv F).toLinearMap)

/-- **The Milnor conjecture in degrees `0` and `1`.**

For every field `F` of characteristic `≠ 2`, the norm residue maps
`k₀(F) → H⁰(G_F, ℤ/2)` and `k₁(F) → H¹(G_F, ℤ/2)` are bijective.
Degree `1` is the Kummer isomorphism `F^×/(F^×)² ≅ H¹(G_F, ℤ/2)`. -/
