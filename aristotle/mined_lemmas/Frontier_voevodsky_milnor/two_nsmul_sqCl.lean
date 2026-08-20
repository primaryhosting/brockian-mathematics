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

theorem two_nsmul_sqCl (x : SqCl F) : (2 : ℕ) • x = 0 := by
  obtain ⟨a, rfl⟩ := sqClass_surjective x
  have h : (2 : ℕ) • sqClass a = sqClass (a ^ 2) := by
    rw [pow_two, sqClass_mul, two_nsmul]
  rw [h, sqClass_eq_zero_iff]
  exact ⟨a, rfl⟩

noncomputable instance : Module (ZMod 2) (SqCl F) := AddCommGroup.zmodModule (two_nsmul_sqCl F)

/-- The `n`-fold tensor power of the square class group over `𝔽₂`. -/
abbrev MilnorTensor (n : ℕ) : Type := PiTensorProduct (ZMod 2) (fun _ : Fin n => SqCl F)

/-- The Steinberg submodule: the span of the tensors of square classes of units
`a₀, …, a_{n-1}` such that two consecutive ones satisfy `aᵢ + aᵢ₊₁ = 1`. -/
