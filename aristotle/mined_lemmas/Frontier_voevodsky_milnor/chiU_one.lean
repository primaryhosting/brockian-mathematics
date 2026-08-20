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

theorem chiU_one (σ : GalF F) : chiU (1 : Fˣ) σ = 0 := by
  have hr : (1 : Ksep F) * 1 = algebraMap F (Ksep F) ((1 : Fˣ) : F) := by simp
  rw [chiU, chi_eq_of_root hr σ]
  simp

