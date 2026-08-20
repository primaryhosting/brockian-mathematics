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

noncomputable def kummerFun (x : SqCl F) (σ : GalF F) : ZMod 2 :=
  Quotient.liftOn' (Additive.toMul x : Fˣ ⧸ sqUnits F) (fun a : Fˣ => chiU a σ) (by
    intro a b hab
    have hmem : a⁻¹ * b ∈ sqUnits F := QuotientGroup.leftRel_apply.1 hab
    obtain ⟨c, hc⟩ := hmem
    have hb : b = a * c ^ 2 := by
      rw [hc]
      group
    subst hb
    show chiU a σ = chiU (a * c ^ 2) σ
    rw [chiU_mul]
    have : chiU (c ^ 2) σ = 0 := by
      rw [pow_two, chiU_mul]
      generalize chiU c σ = z
      revert z
      decide
    rw [this, add_zero])

