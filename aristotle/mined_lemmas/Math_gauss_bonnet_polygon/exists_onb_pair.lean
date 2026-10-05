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

lemma exists_onb_pair (e f : E3) (he : ‖e‖ = 1) (hf : ‖f‖ = 1) (hef : ⟪e, f⟫ = 0) :
    ∃ b : OrthonormalBasis (Fin 3) ℝ E3, b 0 = e ∧ b 1 = f := by
  have hfe : ⟪f, e⟫ = 0 := by rw [real_inner_comm]; exact hef
  have hcard : Module.finrank ℝ E3 = Fintype.card (Fin 3) := by simp
  have horth : Orthonormal ℝ (Set.restrict ({0, 1} : Set (Fin 3)) ![e, f, 0]) := by
    rw [orthonormal_iff_ite]
    rintro ⟨i, hi⟩ ⟨j, hj⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi hj
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;>
      simp [Set.restrict, he, hf, hef, hfe, Subtype.ext_iff]
  obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq hcard horth
  exact ⟨b, by simpa using hb 0 (by simp), by simpa using hb 1 (by simp)⟩

/-- An orthonormal triple in `E3` is an orthonormal basis. -/
