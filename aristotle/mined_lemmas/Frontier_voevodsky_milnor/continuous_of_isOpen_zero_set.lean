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

theorem continuous_of_isOpen_zero_set {H : Type*} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] (f : H → ZMod 2) (hf : ∀ x y, f (x * y) = f x + f y)
    (h : IsOpen {x | f x = 0}) : Continuous f := by
  have key : ∀ v : ZMod 2, IsOpen {x | f x = v} := by
    intro v
    by_cases hne : ∃ x₀, f x₀ = v
    · obtain ⟨x₀, hx₀⟩ := hne
      have hset : {x | f x = v} = (fun y => x₀ * y) '' {y | f y = 0} := by
        ext x
        constructor
        · intro hx
          refine ⟨x₀⁻¹ * x, ?_, by group⟩
          have hx2 := hf x₀ (x₀⁻¹ * x)
          rw [← mul_assoc, mul_inv_cancel, one_mul, hx, hx₀] at hx2
          exact left_eq_add.mp hx2
        · rintro ⟨y, hy, rfl⟩
          simp only [Set.mem_setOf_eq] at hy ⊢
          rw [hf, hy, add_zero, hx₀]
      rw [hset]
      exact (Homeomorph.mulLeft x₀).isOpenMap _ h
    · have hempty : {x | f x = v} = (∅ : Set H) := by
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        exact fun hx => hne ⟨x, hx⟩
      rw [hempty]
      exact isOpen_empty
  rw [continuous_def]
  intro s _
  have hpre : f ⁻¹' s = ⋃ v ∈ s, {x | f x = v} := by
    ext x
    simp
  rw [hpre]
  exact isOpen_biUnion fun v _ => key v

/-- Continuous `n`-cocycles. -/
