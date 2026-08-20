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

theorem chi_eq_zero_iff_of_root {a : F} {r : Ksep F} (hr : r * r = algebraMap F (Ksep F) a)
    (σ : GalF F) : chi a σ = 0 ↔ σ r = r := by
  rw [chi_eq_of_root hr σ]
  by_cases h : σ r = r <;> simp [h]

/-- The character attached to a unit of `F`. -/
