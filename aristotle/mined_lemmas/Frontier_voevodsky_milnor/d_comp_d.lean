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

theorem d_comp_d (n : ℕ) (f : Cochain G n) : d G (n + 1) (d G n f) = 0 := by
  have h := inhomogeneousCochains.d_comp_d (A := Rep.trivial (ZMod 2) G (ZMod 2)) (n := n)
  have h2 := congrArg (fun (m : ModuleCat.Hom _ _) => m.hom f) h
  simpa [d] using h2

/-- The differential out of degree `0` vanishes, since the coefficients are trivial. -/
