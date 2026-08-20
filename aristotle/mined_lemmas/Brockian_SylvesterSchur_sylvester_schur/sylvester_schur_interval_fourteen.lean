import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma sylvester_schur_interval_fourteen {m : ℕ} (hm : 14 < m) :
    ∃ j p : ℕ, j ∈ Set.Ico m (m + 14) ∧ p.Prime ∧ 14 < p ∧ p ∣ j := by
  by_cases hle : 22 ≤ m
  · have hineq0 : (22 + 14 - 1) ^ (14 + 1).primesBelow.card < Nat.choose (22 + 14 - 1) 14 := by
      decide
    have hineq := choose_inequality_of_ge_start (k := 14) (m₀ := 22) (m := m)
      (by omega) (by omega) hle hineq0
    exact exists_large_prime_factor_of_choose_gt_pow_prime_count (m := m) (k := 14)
      (by omega) hm hineq
  · have hlt : m < 22 := Nat.lt_of_not_ge hle
    interval_cases m
    · exact sylvester_schur_interval_prime_witness (p := 17) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact sylvester_schur_interval_prime_witness (p := 17) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact sylvester_schur_interval_prime_witness (p := 17) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact sylvester_schur_interval_prime_witness (p := 19) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact sylvester_schur_interval_prime_witness (p := 19) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact sylvester_schur_interval_prime_witness (p := 23) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact sylvester_schur_interval_prime_witness (p := 23) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

