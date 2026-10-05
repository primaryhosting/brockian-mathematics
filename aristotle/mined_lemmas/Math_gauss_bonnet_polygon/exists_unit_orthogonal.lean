import Mathlib

/-!
# Additive monotone functions on an interval are linear

An elementary Cauchy-functional-equation argument: a nonnegative function on `[0, π]` which is
additive there is determined by its value at `π`.
-/

open scoped Real

namespace Math

variable {W : ℝ → ℝ}

/-- An additive nonnegative function is monotone. -/

lemma exists_unit_orthogonal {u : E3} (hu : ‖u‖ = 1) : ∃ f : E3, ‖f‖ = 1 ∧ ⟪u, f⟫ = 0 := by
  have hu0 : u ≠ 0 := by intro h; rw [h] at hu; simp at hu
  have h1 : Module.finrank ℝ (ℝ ∙ u) = 1 := finrank_span_singleton hu0
  have h2 := Submodule.finrank_add_finrank_orthogonal (K := ℝ ∙ u) (𝕜 := ℝ)
  rw [h1] at h2
  simp only [show Module.finrank ℝ E3 = 3 from by simp] at h2
  have h3 : (ℝ ∙ u)ᴾ ≠ ⊥ := by
    intro h
    rw [h] at h2
    simp at h2
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h3
  refine ⟨‖v‖⁻¹ • v, by simp [norm_smul, hv0], ?_⟩
  rw [real_inner_smul_right]
  have huv : ⟪u, v⟫ = 0 := by
    have := (Submodule.mem_orthogonal _ _).1 hv u (Submodule.mem_span_singleton_self u)
    simpa [real_inner_comm] using this
  simp [huv]

/-- Any pair of unit vectors is a pair in a rotating family, at angles `0` and `angle u v`. -/
