import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

theorem real_deriv_bound_four_thirds {x y : ℝ} (hx_large : (4840 : ℝ) ≤ x)
    (hy_pos : 0 < y) (hy_cube : y ^ (3 : ℕ) ≤ x ^ (4 : ℕ)) :
    √y * (2 + log y) ≤ 2 * x := by
  have hx_nonneg : 0 ≤ x := by linarith
  have hy_nonneg : 0 ≤ y := hy_pos.le
  have hlog : log y ≤ y ^ ((1 : ℝ) / 10) / ((1 : ℝ) / 10) :=
    log_le_rpow_div hy_nonneg (by norm_num)
  have hlog' : log y ≤ 10 * y ^ ((1 : ℝ) / 10) := by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hlog
  have hy_sqrt_le : √y ≤ x ^ ((2 : ℝ) / 3) := by
    rw [sqrt_eq_rpow]
    have h := Real.rpow_le_rpow (by positivity : 0 ≤ y ^ (3 : ℕ)) hy_cube
      (by norm_num : 0 ≤ (1 : ℝ) / 6)
    rw [← Real.rpow_natCast y 3, ← Real.rpow_natCast x 4] at h
    rw [← Real.rpow_mul hy_nonneg, ← Real.rpow_mul hx_nonneg] at h
    norm_num at h
    exact h
  have hy_three_fifths_le : y ^ ((3 : ℝ) / 5) ≤ x ^ ((4 : ℝ) / 5) := by
    have h := Real.rpow_le_rpow (by positivity : 0 ≤ y ^ (3 : ℕ)) hy_cube
      (by norm_num : 0 ≤ (1 : ℝ) / 5)
    rw [← Real.rpow_natCast y 3, ← Real.rpow_natCast x 4] at h
    rw [← Real.rpow_mul hy_nonneg, ← Real.rpow_mul hx_nonneg] at h
    norm_num at h
    exact h
  have hmain_terms : 2 * x ^ ((2 : ℝ) / 3) + 10 * x ^ ((4 : ℝ) / 5) ≤ 2 * x := by
    let t : ℝ := x ^ ((1 : ℝ) / 15)
    have ht_lower : (44 : ℝ) / 25 ≤ t := by
      dsimp [t]
      rw [show (1 : ℝ) / 15 = (15 : ℝ)⁻¹ by norm_num]
      rw [Real.le_rpow_inv_iff_of_pos (by norm_num : 0 ≤ (44 : ℝ) / 25) hx_nonneg
        (by norm_num : 0 < (15 : ℝ))]
      norm_num
      nlinarith
    have hx23 : x ^ ((2 : ℝ) / 3) = t ^ (10 : ℕ) := by
      dsimp [t]
      calc
        x ^ ((2 : ℝ) / 3) = x ^ ((1 : ℝ) / 15 * (10 : ℝ)) := by norm_num
        _ = (x ^ ((1 : ℝ) / 15)) ^ (10 : ℝ) := Real.rpow_mul hx_nonneg _ _
        _ = (x ^ ((1 : ℝ) / 15)) ^ (10 : ℕ) := Real.rpow_natCast _ _
    have hx45 : x ^ ((4 : ℝ) / 5) = t ^ (12 : ℕ) := by
      dsimp [t]
      calc
        x ^ ((4 : ℝ) / 5) = x ^ ((1 : ℝ) / 15 * (12 : ℝ)) := by norm_num
        _ = (x ^ ((1 : ℝ) / 15)) ^ (12 : ℝ) := Real.rpow_mul hx_nonneg _ _
        _ = (x ^ ((1 : ℝ) / 15)) ^ (12 : ℕ) := Real.rpow_natCast _ _
    have hx1 : x = t ^ (15 : ℕ) := by
      dsimp [t]
      calc
        x = x ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ = x ^ ((1 : ℝ) / 15 * (15 : ℝ)) := by norm_num
        _ = (x ^ ((1 : ℝ) / 15)) ^ (15 : ℝ) := Real.rpow_mul hx_nonneg _ _
        _ = (x ^ ((1 : ℝ) / 15)) ^ (15 : ℕ) := Real.rpow_natCast _ _
    rw [hx23, hx45, hx1]
    have htpoly : 0 ≤ 2 * t ^ 5 - 10 * t ^ 2 - 2 := by
      have ht2 : ((44 : ℝ) / 25) ^ 2 ≤ t ^ 2 := by
        nlinarith [sq_nonneg (t - (44 : ℝ) / 25)]
      have ht3 : ((44 : ℝ) / 25) ^ 3 ≤ t ^ 3 := by
        nlinarith [sq_nonneg (t - (44 : ℝ) / 25),
          mul_nonneg (sub_nonneg.mpr ht_lower) (sq_nonneg (t + (44 : ℝ) / 25))]
      nlinarith
    have ht10 : 0 ≤ t ^ 10 := by positivity
    nlinarith [mul_nonneg ht10 htpoly]
  calc
    √y * (2 + log y) ≤ √y * (2 + 10 * y ^ ((1 : ℝ) / 10)) := by gcongr
    _ = 2 * √y + 10 * y ^ ((3 : ℝ) / 5) := by
      rw [sqrt_eq_rpow]
      calc
        y ^ ((1 : ℝ) / 2) * (2 + 10 * y ^ ((1 : ℝ) / 10))
            = 2 * y ^ ((1 : ℝ) / 2) +
                10 * (y ^ ((1 : ℝ) / 2) * y ^ ((1 : ℝ) / 10)) := by ring
        _ = 2 * y ^ ((1 : ℝ) / 2) + 10 * y ^ ((3 : ℝ) / 5) := by
          rw [← Real.rpow_add hy_pos]
          norm_num
    _ ≤ 2 * x ^ ((2 : ℝ) / 3) + 10 * x ^ ((4 : ℝ) / 5) := by gcongr
    _ ≤ 2 * x := hmain_terms

end RealInequalities

