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

noncomputable def d (n : ℕ) : Cochain G n →ₗ[ZMod 2] Cochain G (n + 1) :=
  (inhomogeneousCochains.d (Rep.trivial (ZMod 2) G (ZMod 2)) n).hom

variable {G}

