import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma sylvester_schur_interval_twelve {m : ℕ} (hm : 12 < m) :
    ∃ j p : ℕ, j ∈ Set.Ico m (m + 12) ∧ p.Prime ∧ 12 < p ∧ p ∣ j := by
  by_cases hle : 16 ≤ m
  · have hineq0 : (16 + 12 - 1) ^ (12 + 1).primesBelow.card < Nat.choose (16 + 12 - 1) 12 := by
      decide
    have hineq := choose_inequality_of_ge_start (k := 12) (m₀ := 16) (m := m)
      (by omega) (by omega) hle hineq0
    exact exists_large_prime_factor_of_choose_gt_pow_prime_count (m := m) (k := 12)
      (by omega) hm hineq
  · have hlt : m < 16 := Nat.lt_of_not_ge hle
    interval_cases m
    · exact ⟨13, 13, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨17, 17, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨17, 17, by norm_num, by norm_num, by norm_num, by norm_num⟩

