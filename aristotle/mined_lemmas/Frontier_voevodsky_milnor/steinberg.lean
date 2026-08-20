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

noncomputable def steinberg (n : ℕ) : Submodule (ZMod 2) (MilnorTensor F n) :=
  Submodule.span (ZMod 2)
    {t | ∃ (v : Fin n → Fˣ) (i : ℕ) (hi : i + 1 < n),
      ((v ⟨i, Nat.lt_of_succ_lt hi⟩ : F) + (v ⟨i + 1, hi⟩ : F) = 1) ∧
        t = PiTensorProduct.tprod (ZMod 2) fun j => sqClass (v j)}

/-- The `n`-th mod-2 Milnor K-group `k_n(F) = K^M_n(F)/2`. -/
abbrev MilnorK2 (n : ℕ) : Type := MilnorTensor F n ⧸ steinberg F n

