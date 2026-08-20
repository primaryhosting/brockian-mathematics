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

theorem coboundaries_le_cocycles (n : ℕ) : coboundaries G n ≤ cocycles G n := by
  cases n with
  | zero => simp [coboundaries]
  | succ n =>
    rintro _ ⟨f, hf, rfl⟩
    exact ⟨continuous_d G hf, d_comp_d n f⟩

/-- The `n`-th continuous cohomology group of `G` with coefficients in the trivial
module `ZMod 2`. -/
abbrev H (n : ℕ) : Type :=
  (cocycles G n) ⧸ (Submodule.comap (cocycles G n).subtype (coboundaries G n))

noncomputable instance (n : ℕ) : AddCommGroup (H G n) := inferInstance
noncomputable instance (n : ℕ) : Module (ZMod 2) (H G n) := inferInstance

/-- The projection from cocycles to cohomology. -/
