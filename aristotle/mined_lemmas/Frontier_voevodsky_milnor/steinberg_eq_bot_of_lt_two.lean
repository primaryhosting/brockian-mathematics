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

theorem steinberg_eq_bot_of_lt_two {n : ℕ} (hn : n < 2) : steinberg F n = ⊥ := by
  rw [steinberg, Submodule.span_eq_bot]
  rintro t ⟨v, i, hi, -, rfl⟩
  omega

/-- `k_0(F) ≅ 𝔽₂`. -/
