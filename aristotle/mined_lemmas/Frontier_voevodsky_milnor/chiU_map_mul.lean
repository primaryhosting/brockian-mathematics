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

theorem chiU_map_mul (a : Fˣ) (σ τ : GalF F) : chiU a (σ * τ) = chiU a σ + chiU a τ := by
  have hra : sqrtOf F (a : F) * sqrtOf F (a : F) = algebraMap F (Ksep F) (a : F) :=
    sqrtOf_mul_self F _
  have hra0 := sqrtOf_ne_zero a
  simp only [chiU]
  rw [chi_eq_of_root hra, chi_eq_of_root hra, chi_eq_of_root hra]
  rcases aut_root_eq_or_neg hra σ with h1 | h1 <;> rcases aut_root_eq_or_neg hra τ with h2 | h2 <;>
    rw [AlgEquiv.mul_apply, h2] <;>
    simp [h1, map_neg, neg_neg, neg_ne_self_of_ne_zero hra0]
  decide

