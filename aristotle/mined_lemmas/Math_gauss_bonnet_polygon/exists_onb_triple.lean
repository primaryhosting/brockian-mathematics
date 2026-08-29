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

lemma exists_onb_triple (e f g : E3) (he : ‖e‖ = 1) (hf : ‖f‖ = 1) (hg : ‖g‖ = 1)
    (hef : ⟪e, f⟫ = 0) (heg : ⟪e, g⟫ = 0) (hfg : ⟪f, g⟫ = 0) :
    ∃ b : OrthonormalBasis (Fin 3) ℝ E3, b 0 = e ∧ b 1 = f ∧ b 2 = g := by
  have hfe : ⟪f, e⟫ = 0 := by rw [real_inner_comm]; exact hef
  have hge : ⟪g, e⟫ = 0 := by rw [real_inner_comm]; exact heg
  have hgf : ⟪g, f⟫ = 0 := by rw [real_inner_comm]; exact hfg
  have hcard : Module.finrank ℝ E3 = Fintype.card (Fin 3) := by simp
  have horth : Orthonormal ℝ (Set.restrict (Set.univ : Set (Fin 3)) ![e, f, g]) := by
    rw [orthonormal_iff_ite]
    rintro ⟨i, hi⟩ ⟨j, hj⟩
    fin_cases i <;> fin_cases j <;>
      simp [Set.restrict, he, hf, hg, hef, heg, hfg, hfe, hge, hgf, Subtype.ext_iff]
  obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq hcard horth
  exact ⟨b, by simpa using hb 0 (by simp), by simpa using hb 1 (by simp),
    by simpa using hb 2 (by simp)⟩

/-- Any orthonormal pair can be mapped to any other by a linear isometry of `E3`. -/
