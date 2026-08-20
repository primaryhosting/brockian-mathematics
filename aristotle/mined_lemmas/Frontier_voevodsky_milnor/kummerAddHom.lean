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

noncomputable def kummerAddHom : SqCl F →+ ContCoh.Cochain (GalF F) 1 where
  toFun x := fun g => kummerFun F x (g 0)
  map_zero' := by
    ext g
    have : (0 : SqCl F) = sqClass (1 : Fˣ) := rfl
    rw [this, kummerFun_sqClass, chiU_one]
    rfl
  map_add' x y := by
    obtain ⟨a, rfl⟩ := sqClass_surjective x
    obtain ⟨b, rfl⟩ := sqClass_surjective y
    ext g
    rw [← sqClass_mul]
    simp only [kummerFun_sqClass]
    rw [chiU_mul]
    rfl

