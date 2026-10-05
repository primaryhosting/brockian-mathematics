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

lemma exists_dirv_repr {u v : E3} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ∃ e f : E3, ‖e‖ = 1 ∧ ‖f‖ = 1 ∧ ⟪e, f⟫ = 0 ∧
      u = dirv e f 0 ∧ v = dirv e f (angle u v) := by
  set ψ := angle u v with hψ
  have hcos : Real.cos ψ = ⟪u, v⟫ := by
    rw [hψ, InnerProductGeometry.cos_angle, hu, hv]
    simp
  have hsin : Real.sin ψ = ‖v - ⟪v, u⟫ • u‖ := by
    have hnn : 0 ≤ Real.sin ψ :=
      Real.sin_nonneg_of_nonneg_of_le_pi (angle_nonneg u v) (angle_le_pi u v)
    have huu : ⟪u, u⟫ = (1 : ℝ) := by rw [real_inner_self_eq_norm_sq, hu]; norm_num
    have hvv : ⟪v, v⟫ = (1 : ℝ) := by rw [real_inner_self_eq_norm_sq, hv]; norm_num
    have hnorm : ‖v - ⟪v, u⟫ • u‖ ^ 2 = 1 - ⟪u, v⟫ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq]
      simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
        huu, hvv, real_inner_comm v u]
      ring
    have hs2 : Real.sin ψ ^ 2 = 1 - ⟪u, v⟫ ^ 2 := by
      have := Real.sin_sq_add_cos_sq ψ
      rw [hcos] at this
      linarith
    nlinarith [norm_nonneg (v - ⟪v, u⟫ • u)]
  by_cases hw : v - ⟪v, u⟫ • u = 0
  · obtain ⟨f, hf, huf⟩ := exists_unit_orthogonal hu
    refine ⟨u, f, hu, hf, huf, (dirv_zero u f).symm, ?_⟩
    have hs0 : Real.sin ψ = 0 := by rw [hsin, hw, norm_zero]
    have hvu : v = ⟪v, u⟫ • u := by
      have := sub_eq_zero.1 hw
      exact this
    rw [dirv, hs0, hcos, real_inner_comm u v, ← hvu]
    simp
  · set w := v - ⟪v, u⟫ • u with hwdef
    have hwn : ‖w‖ ≠ 0 := by simpa using hw
    refine ⟨u, ‖w‖⁻¹ • w, hu, by simp [norm_smul, hwn], ?_, (dirv_zero _ _).symm, ?_⟩
    · have huu : ⟪u, u⟫ = (1 : ℝ) := by rw [real_inner_self_eq_norm_sq, hu]; norm_num
      rw [real_inner_smul_right, hwdef, inner_sub_right, real_inner_smul_right, huu,
        real_inner_comm u v]
      ring
    · rw [dirv, hcos, hsin, real_inner_comm u v, smul_smul, mul_inv_cancel₀ hwn, one_smul,
        hwdef]
      abel

/-- **The wedge volume formula**: the part of the unit ball lying in the two half-spaces with
unit inner normals `u` and `v` has volume `2/3 * (π - angle u v)`. -/
