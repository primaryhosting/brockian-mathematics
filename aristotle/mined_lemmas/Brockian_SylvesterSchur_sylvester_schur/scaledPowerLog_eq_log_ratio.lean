import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma scaledPowerLog_eq_log_ratio {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    scaledPowerLog x y = log (x * y ^ √y / (y / (2 * x)) ^ x) := by
  unfold scaledPowerLog
  rw [log_div (mul_pos hx (rpow_pos_of_pos hy _)).ne'
      (rpow_pos_of_pos (div_pos hy (mul_pos two_pos hx)) _).ne',
    log_mul hx.ne' (rpow_pos_of_pos hy _).ne',
    log_rpow hy, log_rpow (div_pos hy (mul_pos two_pos hx))]

