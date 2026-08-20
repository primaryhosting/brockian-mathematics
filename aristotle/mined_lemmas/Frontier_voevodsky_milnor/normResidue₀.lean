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

noncomputable def normResidue₀ : MilnorK2 F 0 →ₗ[ZMod 2] ContCoh.H (GalF F) 0 :=
  (ContCoh.H0Equiv (GalF F)).symm.toLinearMap ∘ₗ (milnorK2ZeroEquiv F).toLinearMap

/-- The norm residue map in degree `1`: the Kummer map
`k₁(F) = F^×/(F^×)² → H¹(G_F, ℤ/2)`, `a ↦ (σ ↦ σ(√a)/√a)`. -/
