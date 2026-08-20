import Mathlib
namespace C4.IT4

/-- The fundamental logarithm bound `log x ≤ x - 1` for positive `x`. -/

theorem gibbs_two' (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (hpq : p ≤ 1) (hqq : q < 1) :
    0 ≤ p * Real.log (p/q) + (1-p) * Real.log ((1-p)/(1-q)) := by
  have hq1 : 0 < 1 - q := by linarith
  rcases eq_or_lt_of_le hpq with rfl | hp1
  · have hlog : Real.log q ≤ 0 := Real.log_nonpos hq.le hqq.le
    simp only [sub_self, zero_mul, add_zero, one_mul]
    rw [Real.log_div one_ne_zero hq.ne', Real.log_one]
    linarith
  · have hp1' : 0 < 1 - p := by linarith
    have hA : p * (Real.log q - Real.log p) ≤ q - p := by
      have h := Real.log_le_sub_one_of_pos (div_pos hq hp)
      rw [Real.log_div hq.ne' hp.ne'] at h
      have := mul_le_mul_of_nonneg_left h hp.le
      calc p * (Real.log q - Real.log p) ≤ p * (q / p - 1) := this
        _ = q - p := by field_simp
    have hB : (1 - p) * (Real.log (1-q) - Real.log (1-p)) ≤ p - q := by
      have h := Real.log_le_sub_one_of_pos (div_pos hq1 hp1')
      rw [Real.log_div hq1.ne' hp1'.ne'] at h
      have := mul_le_mul_of_nonneg_left h hp1'.le
      calc (1 - p) * (Real.log (1-q) - Real.log (1-p)) ≤ (1 - p) * ((1-q) / (1-p) - 1) := this
        _ = p - q := by field_simp; ring
    rw [Real.log_div hp.ne' hq.ne', Real.log_div hp1'.ne' hq1.ne']
    linarith

end C4.IT4

