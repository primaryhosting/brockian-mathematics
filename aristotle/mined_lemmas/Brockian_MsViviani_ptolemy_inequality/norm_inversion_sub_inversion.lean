import Mathlib
namespace Brockian.MsViviani

/-- The inversion map `x ↦ ‖x‖⁻² • x` scales distances by `(‖x‖ * ‖y‖)⁻¹`. -/

private lemma norm_inversion_sub_inversion {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (x y : E) (hx : x ≠ 0) (hy : y ≠ 0) :
    ‖(‖x‖ ^ 2)⁻¹ • x - (‖y‖ ^ 2)⁻¹ • y‖ = ‖x - y‖ / (‖x‖ * ‖y‖) := by
  have hx' : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hy' : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy
  have hxy : ‖x‖ * ‖y‖ ≠ 0 := mul_ne_zero hx' hy'
  -- The key is to show ‖‖y‖² • x - ‖x‖² • y‖ = ‖x‖ * ‖y‖ * ‖x - y‖
  have key : ‖‖y‖ ^ 2 • x - ‖x‖ ^ 2 • y‖ = ‖x‖ * ‖y‖ * ‖x - y‖ := by
    have h1 : ‖‖y‖ ^ 2 • x - ‖x‖ ^ 2 • y‖ ^ 2 = (‖x‖ * ‖y‖ * ‖x - y‖) ^ 2 := by
      rw [norm_sub_sq_real]
      simp [norm_smul, inner_smul_left, inner_smul_right]
      nth_rw 2 [mul_pow, mul_pow]
      rw [norm_sub_sq_real]
      rw [real_inner_comm y x]
      ring
    exact (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (mul_nonneg (norm_nonneg x) (norm_nonneg y)) (norm_nonneg _))).mp h1
  -- Rewrite LHS using common factor
  have h2 : (‖x‖ ^ 2)⁻¹ • x - (‖y‖ ^ 2)⁻¹ • y = (‖x‖ ^ 2 * ‖y‖ ^ 2)⁻¹ • (‖y‖ ^ 2 • x - ‖x‖ ^ 2 • y) := by
    rw [smul_sub]
    congr 1
    · rw [smul_smul]
      field_simp
    · rw [smul_smul]
      field_simp
  rw [h2, norm_smul, key]
  have h3 : ‖(‖x‖ ^ 2 * ‖y‖ ^ 2)⁻¹‖ = (‖x‖ ^ 2 * ‖y‖ ^ 2)⁻¹ := by
    rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (mul_nonneg (sq_nonneg _) (sq_nonneg _)))]
  rw [h3]
  field_simp

/-- Ptolemy's inequality, vector form, in the case where all three vectors are nonzero. -/
