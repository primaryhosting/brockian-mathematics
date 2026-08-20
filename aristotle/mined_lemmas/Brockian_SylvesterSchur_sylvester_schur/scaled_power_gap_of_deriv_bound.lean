import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma scaled_power_gap_of_deriv_bound {n i : ℕ} (hi_large : 4840 ≤ i)
    (hi_half : i ≤ n / 2) (hn_lower : 5 * i ≤ 2 * n)
    (hderiv : ∀ z ∈ Set.Icc (((5 : ℝ) / 2) * i) n,
      √z * (2 + log z) ≤ 2 * (i : ℝ)) :
    i * ((2 * i) ^ i * n ^ n.sqrt) < n ^ i := by
  have hi_pos_nat : 0 < i := by omega
  have hn_pos_nat : 0 < n := by omega
  have hx_large : (4840 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi_large
  have hy_lower : (5 : ℝ) / 2 * (i : ℝ) ≤ (n : ℝ) := by
    nlinarith [show (5 : ℝ) * i ≤ 2 * (n : ℝ) by exact_mod_cast hn_lower]
  have hreal :=
    real_scaled_power_of_deriv_bound (x := (i : ℝ)) (y := (n : ℝ))
      hx_large hy_lower hderiv
  have hpow_le : (n : ℝ) ^ n.sqrt ≤ (n : ℝ) ^ √(n : ℝ) := by
    calc
      (n : ℝ) ^ n.sqrt = (n : ℝ) ^ (n.sqrt : ℝ) := by rw [Real.rpow_natCast]
      _ ≤ (n : ℝ) ^ √(n : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le
          (by exact_mod_cast (Nat.succ_le_of_lt hn_pos_nat)) Real.nat_sqrt_le_real_sqrt
  have hreal_nat_sqrt :
      (i : ℝ) * (n : ℝ) ^ n.sqrt < ((n : ℝ) / (2 * (i : ℝ))) ^ (i : ℝ) := by
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hpow_le (by positivity)) hreal
  have hmul_pos : 0 < (2 * (i : ℝ)) ^ i := pow_pos (by positivity) i
  have hreal_scaled :
      (i : ℝ) * ((2 * i : ℕ) ^ i * (n ^ n.sqrt : ℕ)) < (n : ℝ) ^ i := by
    calc
      (i : ℝ) * ((2 * i : ℕ) ^ i * (n ^ n.sqrt : ℕ))
          = (2 * (i : ℝ)) ^ i * ((i : ℝ) * (n : ℝ) ^ n.sqrt) := by
            norm_num [mul_assoc, mul_comm, mul_left_comm]
      _ < (2 * (i : ℝ)) ^ i * (((n : ℝ) / (2 * (i : ℝ))) ^ (i : ℝ)) :=
            mul_lt_mul_of_pos_left hreal_nat_sqrt hmul_pos
      _ = (n : ℝ) ^ i := by
            rw [← Real.rpow_natCast]
            rw [← Real.mul_rpow (by positivity : 0 ≤ 2 * (i : ℝ))
              (by positivity : 0 ≤ (n : ℝ) / (2 * (i : ℝ)))]
            have hbase : (2 * (i : ℝ)) * ((n : ℝ) / (2 * (i : ℝ))) = (n : ℝ) := by
              field_simp [(by positivity : (2 * (i : ℝ)) ≠ 0)]
            rw [hbase, Real.rpow_natCast]
  exact_mod_cast hreal_scaled

end ScaledPowerDerivativeGap

