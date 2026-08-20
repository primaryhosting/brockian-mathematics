import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma sylvester_schur_interval_five {m : ℕ} (hm : 5 < m) :
    ∃ j p : ℕ, j ∈ Set.Ico m (m + 5) ∧ p.Prime ∧ 5 < p ∧ p ∣ j := by
  by_cases hle : 12 ≤ m
  · have hineq0 : (12 + 5 - 1) ^ (5 + 1).primesBelow.card < Nat.choose (12 + 5 - 1) 5 := by
      decide
    have hineq := choose_inequality_of_ge_start (k := 5) (m₀ := 12) (m := m)
      (by omega) (by omega) hle hineq0
    exact exists_large_prime_factor_of_choose_gt_pow_prime_count (m := m) (k := 5)
      (by omega) hm hineq
  · have hlt : m < 12 := Nat.lt_of_not_ge hle
    interval_cases m
    · exact ⟨7, 7, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨7, 7, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨11, 11, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨11, 11, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨11, 11, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨11, 11, by norm_num, by norm_num, by norm_num, by norm_num⟩

