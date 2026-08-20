import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma sylvester_schur_interval_seventeen {m : ℕ} (hm : 17 < m) :
    ∃ j p : ℕ, j ∈ Set.Ico m (m + 17) ∧ p.Prime ∧ 17 < p ∧ p ∣ j := by
  by_cases hle : 26 ≤ m
  · have hineq0 : (26 + 17 - 1) ^ (17 + 1).primesBelow.card < Nat.choose (26 + 17 - 1) 17 := by
      decide
    have hineq := choose_inequality_of_ge_start (k := 17) (m₀ := 26) (m := m)
      (by omega) (by omega) hle hineq0
    exact exists_large_prime_factor_of_choose_gt_pow_prime_count (m := m) (k := 17)
      (by omega) hm hineq
  · have hlt : m < 26 := Nat.lt_of_not_ge hle
    interval_cases m
    · exact sylvester_schur_interval_prime_witness (p := 19) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact sylvester_schur_interval_prime_witness (p := 19) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact sylvester_schur_interval_prime_witness (p := 23) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact sylvester_schur_interval_prime_witness (p := 23) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact sylvester_schur_interval_prime_witness (p := 23) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact sylvester_schur_interval_prime_witness (p := 23) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact sylvester_schur_interval_prime_witness (p := 29) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact sylvester_schur_interval_prime_witness (p := 29) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

