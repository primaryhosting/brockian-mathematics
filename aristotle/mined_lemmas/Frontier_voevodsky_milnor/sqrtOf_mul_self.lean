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

theorem sqrtOf_mul_self (a : F) : sqrtOf F a * sqrtOf F a = algebraMap F (Ksep F) a :=
  ((IsSepClosed.exists_eq_mul_self (algebraMap F (Ksep F) a)).choose_spec).symm

variable {F}

/-- Two square roots of the same element differ by a sign. -/
