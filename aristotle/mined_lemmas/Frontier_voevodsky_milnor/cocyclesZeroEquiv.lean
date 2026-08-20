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

noncomputable def cocyclesZeroEquiv : (cocycles G 0) ≃ₗ[ZMod 2] ZMod 2 where
  toFun f := (f : Cochain G 0) (fun i => i.elim0)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun c := ⟨fun _ => c, continuous_const, d_zero_eq_zero _⟩
  left_inv f := by
    ext g
    exact congrArg (f : Cochain G 0) (Subsingleton.elim (fun i : Fin 0 => i.elim0) g)
  right_inv c := rfl

/-- In degree `0`, every cochain is a cocycle, and cohomology is `ZMod 2`. -/
