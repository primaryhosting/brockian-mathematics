import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma sylvester_schur_interval_sixteen {m : ℕ} (hm : 16 < m) :
    ∃ j p : ℕ, j ∈ Set.Ico m (m + 16) ∧ p.Prime ∧ 16 < p ∧ p ∣ j := by
  by_cases hle : 19 ≤ m
  · have hineq0 : (19 + 16 - 1) ^ (16 + 1).primesBelow.card < Nat.choose (19 + 16 - 1) 16 := by
      decide
    have hineq := choose_inequality_of_ge_start (k := 16) (m₀ := 19) (m := m)
      (by omega) (by omega) hle hineq0
    exact exists_large_prime_factor_of_choose_gt_pow_prime_count (m := m) (k := 16)
      (by omega) hm hineq
  · have hlt : m < 19 := Nat.lt_of_not_ge hle
    interval_cases m
    · exact sylvester_schur_interval_prime_witness (p := 17) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact sylvester_schur_interval_prime_witness (p := 19) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

