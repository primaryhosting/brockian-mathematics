import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma sylvester_schur_interval_twenty {m : ℕ} (hm : 20 < m) :
    ∃ j p : ℕ, j ∈ Set.Ico m (m + 20) ∧ p.Prime ∧ 20 < p ∧ p ∣ j := by
  by_cases hle : 31 ≤ m
  · have hineq0 : (31 + 20 - 1) ^ (20 + 1).primesBelow.card < Nat.choose (31 + 20 - 1) 20 := by
      decide
    have hineq := choose_inequality_of_ge_start (k := 20) (m₀ := 31) (m := m)
      (by omega) (by omega) hle hineq0
    exact exists_large_prime_factor_of_choose_gt_pow_prime_count (m := m) (k := 20)
      (by omega) hm hineq
  · have hlt : m < 31 := Nat.lt_of_not_ge hle
    interval_cases m
    · exact sylvester_schur_interval_prime_witness (p := 23) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact sylvester_schur_interval_prime_witness (p := 23) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact sylvester_schur_interval_prime_witness (p := 23) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact sylvester_schur_interval_prime_witness (p := 29) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact sylvester_schur_interval_prime_witness (p := 29) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact sylvester_schur_interval_prime_witness (p := 29) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact sylvester_schur_interval_prime_witness (p := 29) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact sylvester_schur_interval_prime_witness (p := 29) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact sylvester_schur_interval_prime_witness (p := 29) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact sylvester_schur_interval_prime_witness (p := 31) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

