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

theorem aut_root_eq_or_neg {a : F} {r : Ksep F} (hr : r * r = algebraMap F (Ksep F) a)
    (σ : GalF F) : σ r = r ∨ σ r = -r := by
  have h : (σ r) * (σ r) = r * r := by
    rw [← map_mul, hr, AlgEquiv.commutes]
  exact eq_or_eq_neg_of_mul_self_eq h.symm

/-- The character `χ_a : G_F → ℤ/2` attached to `a ∈ F`. -/
