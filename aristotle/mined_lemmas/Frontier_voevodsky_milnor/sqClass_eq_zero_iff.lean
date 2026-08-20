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

theorem sqClass_eq_zero_iff {a : Fˣ} : sqClass a = 0 ↔ ∃ b : Fˣ, b ^ 2 = a := by
  constructor
  · intro h
    have : (QuotientGroup.mk a : Fˣ ⧸ sqUnits F) = 1 := h
    rw [QuotientGroup.eq_one_iff] at this
    exact this
  · rintro ⟨b, rfl⟩
    have : (QuotientGroup.mk (b ^ 2) : Fˣ ⧸ sqUnits F) = 1 :=
      (QuotientGroup.eq_one_iff _).2 ⟨b, rfl⟩
    exact this

variable (F)

