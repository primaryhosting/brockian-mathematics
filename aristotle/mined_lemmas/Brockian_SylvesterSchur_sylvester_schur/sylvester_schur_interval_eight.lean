import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma sylvester_schur_interval_eight {m : ℕ} (hm : 8 < m) :
    ∃ j p : ℕ, j ∈ Set.Ico m (m + 8) ∧ p.Prime ∧ 8 < p ∧ p ∣ j := by
  by_cases hle : 14 ≤ m
  · have hineq0 : (14 + 8 - 1) ^ (8 + 1).primesBelow.card < Nat.choose (14 + 8 - 1) 8 := by
      decide
    have hineq := choose_inequality_of_ge_start (k := 8) (m₀ := 14) (m := m)
      (by omega) (by omega) hle hineq0
    exact exists_large_prime_factor_of_choose_gt_pow_prime_count (m := m) (k := 8)
      (by omega) hm hineq
  · have hlt : m < 14 := Nat.lt_of_not_ge hle
    interval_cases m
    · exact ⟨11, 11, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨11, 11, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨11, 11, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨13, 13, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨13, 13, by norm_num, by norm_num, by norm_num, by norm_num⟩

