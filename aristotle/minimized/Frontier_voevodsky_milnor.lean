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

def sqUnits : Subgroup Fˣ where
  carrier := {x | ∃ y : Fˣ, y ^ 2 = x}
  one_mem' := ⟨1, one_pow 2⟩
  mul_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a * b, by rw [mul_pow]⟩
  inv_mem' := by
    rintro _ ⟨a, rfl⟩
    exact ⟨a⁻¹, by rw [inv_pow]⟩

/-- The group of square classes `F^× / (F^×)²`, written additively. This is `k_1(F)`. -/

def SqCl : Type := Additive (Fˣ ⧸ sqUnits F)

noncomputable instance : AddCommGroup (SqCl F) :=
  inferInstanceAs (AddCommGroup (Additive (Fˣ ⧸ sqUnits F)))

variable {F}

/-- The square class of a unit. -/

def sqClass (a : Fˣ) : SqCl F := Additive.ofMul (QuotientGroup.mk a)

noncomputable def steinberg (n : ℕ) : Submodule (ZMod 2) (MilnorTensor F n) :=
  Submodule.span (ZMod 2)
    {t | ∃ (v : Fin n → Fˣ) (i : ℕ) (hi : i + 1 < n),
      ((v ⟨i, Nat.lt_of_succ_lt hi⟩ : F) + (v ⟨i + 1, hi⟩ : F) = 1) ∧
        t = PiTensorProduct.tprod (ZMod 2) fun j => sqClass (v j)}

/-- The `n`-th mod-2 Milnor K-group `k_n(F) = K^M_n(F)/2`. -/
abbrev MilnorK2 (n : ℕ) : Type := MilnorTensor F n ⧸ steinberg F n

theorem steinberg_eq_bot_of_lt_two {n : ℕ} (hn : n < 2) : steinberg F n = ⊥ := by
  rw [steinberg, Submodule.span_eq_bot]
  rintro t ⟨v, i, hi, -, rfl⟩
  omega

/-- `k_0(F) ≅ 𝔽₂`. -/

noncomputable def milnorK2ZeroEquiv : MilnorK2 F 0 ≃ₗ[ZMod 2] ZMod 2 :=
  (Submodule.quotEquivOfEqBot _ (steinberg_eq_bot_of_lt_two F (by norm_num))).trans
    (PiTensorProduct.isEmptyEquiv (Fin 0))

/-- `k_1(F) ≅ F^×/(F^×)²`. -/
