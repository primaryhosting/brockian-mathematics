import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma sylvester_schur_interval_fifteen {m : ℕ} (hm : 15 < m) :
    ∃ j p : ℕ, j ∈ Set.Ico m (m + 15) ∧ p.Prime ∧ 15 < p ∧ p ∣ j := by
  by_cases hle : 20 ≤ m
  · have hineq0 : (20 + 15 - 1) ^ (15 + 1).primesBelow.card < Nat.choose (20 + 15 - 1) 15 := by
      decide
    have hineq := choose_inequality_of_ge_start (k := 15) (m₀ := 20) (m := m)
      (by omega) (by omega) hle hineq0
    exact exists_large_prime_factor_of_choose_gt_pow_prime_count (m := m) (k := 15)
      (by omega) hm hineq
  · have hlt : m < 20 := Nat.lt_of_not_ge hle
    interval_cases m
    · exact sylvester_schur_interval_prime_witness (p := 17) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact sylvester_schur_interval_prime_witness (p := 17) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact sylvester_schur_interval_prime_witness (p := 19) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact sylvester_schur_interval_prime_witness (p := 19) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

