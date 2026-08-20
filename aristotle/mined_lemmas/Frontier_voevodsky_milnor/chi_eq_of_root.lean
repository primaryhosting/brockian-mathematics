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

theorem chi_eq_of_root {a : F} {r : Ksep F} (hr : r * r = algebraMap F (Ksep F) a) (σ : GalF F) :
    chi a σ = if σ r = r then 0 else 1 := by
  have hs := sqrtOf_mul_self F a
  rcases eq_or_eq_neg_of_mul_self_eq (hr.trans hs.symm) with h | h
  · unfold chi; rw [h]
  · unfold chi; rw [h, map_neg]; simp only [neg_inj]

/-- In characteristic `≠ 2`, a nonzero element of the separable closure differs from its
negative. -/
