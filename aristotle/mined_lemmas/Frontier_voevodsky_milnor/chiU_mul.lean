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

theorem chiU_mul (a b : Fˣ) (σ : GalF F) : chiU (a * b) σ = chiU a σ + chiU b σ := by
  have hra : sqrtOf F (a : F) * sqrtOf F (a : F) = algebraMap F (Ksep F) (a : F) :=
    sqrtOf_mul_self F _
  have hrb : sqrtOf F (b : F) * sqrtOf F (b : F) = algebraMap F (Ksep F) (b : F) :=
    sqrtOf_mul_self F _
  have hrab : (sqrtOf F (a : F) * sqrtOf F (b : F)) * (sqrtOf F (a : F) * sqrtOf F (b : F))
      = algebraMap F (Ksep F) ((a * b : Fˣ) : F) := by
    rw [Units.val_mul, map_mul, ← hra, ← hrb]; ring
  have hra0 := sqrtOf_ne_zero a
  have hrb0 := sqrtOf_ne_zero b
  have hab0 : sqrtOf F (a : F) * sqrtOf F (b : F) ≠ 0 := mul_ne_zero hra0 hrb0
  simp only [chiU]
  rw [chi_eq_of_root hrab, chi_eq_of_root hra, chi_eq_of_root hrb]
  rcases aut_root_eq_or_neg hra σ with h1 | h1 <;> rcases aut_root_eq_or_neg hrb σ with h2 | h2 <;>
    rw [map_mul, h1, h2] <;>
    simp [mul_neg, neg_mul, neg_neg, neg_ne_self_of_ne_zero hab0, neg_ne_self_of_ne_zero hra0,
      neg_ne_self_of_ne_zero hrb0]
  decide

