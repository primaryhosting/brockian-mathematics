import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma central_gap_of_le_five_halves {n i : ℕ} (hi_large : 4410 ≤ i)
    (hi_half : i ≤ n / 2) (hn_le : 2 * n ≤ 5 * i) :
    i * (n ^ n.sqrt * 4 ^ (n / 3)) < 4 ^ i := by
  let B : ℝ := (5 : ℝ) / 2 * i
  have hn_pos : 0 < n := by omega
  have hn_real_le : (n : ℝ) ≤ B := by
    dsimp [B]
    nlinarith [show (2 : ℝ) * n ≤ (5 : ℝ) * i by exact_mod_cast hn_le]
  have hbase_ge_one : (1 : ℝ) ≤ B := by
    dsimp [B]
    nlinarith [show (1 : ℝ) ≤ i by exact_mod_cast (by omega : 1 ≤ i)]
  have hn_pow_le : (n : ℝ) ^ n.sqrt ≤ B ^ √B := by
    calc
      (n : ℝ) ^ n.sqrt = (n : ℝ) ^ (n.sqrt : ℝ) := by
        rw [Real.rpow_natCast]
      _ ≤ (n : ℝ) ^ √(n : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le
          (by exact_mod_cast (Nat.succ_le_of_lt hn_pos)) Real.nat_sqrt_le_real_sqrt
      _ ≤ B ^ √(n : ℝ) :=
        Real.rpow_le_rpow (by positivity) hn_real_le (Real.sqrt_nonneg _)
      _ ≤ B ^ √B :=
        Real.rpow_le_rpow_of_exponent_le hbase_ge_one (Real.sqrt_le_sqrt hn_real_le)
  have hdiv_le : ((n / 3 : ℕ) : ℝ) ≤ B / 3 := by
    calc
      ((n / 3 : ℕ) : ℝ) ≤ (n : ℝ) / 3 := Nat.cast_div_le
      _ ≤ B / 3 := by gcongr
  have hfour_le : (4 : ℝ) ^ (n / 3) ≤ 4 ^ (B / 3) := by
    calc
      (4 : ℝ) ^ (n / 3) = (4 : ℝ) ^ ((n / 3 : ℕ) : ℝ) := by
        rw [Real.rpow_natCast]
      _ ≤ 4 ^ (B / 3) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hdiv_le
  have hrealB : (i : ℝ) * B ^ √B * 4 ^ (B / 3) < 4 ^ (i : ℝ) := by
    simpa [B] using
      real_central_gap_five_halves (x := (i : ℝ)) (by exact_mod_cast hi_large)
  have hcast : ((i * (n ^ n.sqrt * 4 ^ (n / 3))) : ℝ) < ((4 ^ i) : ℝ) := by
    calc
      (i : ℝ) * ((n : ℝ) ^ n.sqrt * (4 : ℝ) ^ (n / 3))
          ≤ (i : ℝ) * (B ^ √B * 4 ^ (B / 3)) := by
            gcongr
      _ = (i : ℝ) * B ^ √B * 4 ^ (B / 3) := by ring
      _ < 4 ^ (i : ℝ) := hrealB
      _ = (4 : ℝ) ^ i := by rw [Real.rpow_natCast]
  exact_mod_cast hcast

