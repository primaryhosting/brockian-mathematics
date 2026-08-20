import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma sylvester_schur_interval_eleven {m : ℕ} (hm : 11 < m) :
    ∃ j p : ℕ, j ∈ Set.Ico m (m + 11) ∧ p.Prime ∧ 11 < p ∧ p ∣ j := by
  by_cases hle : 18 ≤ m
  · have hineq0 : (18 + 11 - 1) ^ (11 + 1).primesBelow.card < Nat.choose (18 + 11 - 1) 11 := by
      decide
    have hineq := choose_inequality_of_ge_start (k := 11) (m₀ := 18) (m := m)
      (by omega) (by omega) hle hineq0
    exact exists_large_prime_factor_of_choose_gt_pow_prime_count (m := m) (k := 11)
      (by omega) hm hineq
  · have hlt : m < 18 := Nat.lt_of_not_ge hle
    interval_cases m
    · exact ⟨13, 13, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨13, 13, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨17, 17, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨17, 17, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨17, 17, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨17, 17, by norm_num, by norm_num, by norm_num, by norm_num⟩

