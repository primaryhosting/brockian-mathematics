import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma sylvester_schur_interval_nine {m : ℕ} (hm : 9 < m) :
    ∃ j p : ℕ, j ∈ Set.Ico m (m + 9) ∧ p.Prime ∧ 9 < p ∧ p ∣ j := by
  by_cases hle : 12 ≤ m
  · have hineq0 : (12 + 9 - 1) ^ (9 + 1).primesBelow.card < Nat.choose (12 + 9 - 1) 9 := by
      decide
    have hineq := choose_inequality_of_ge_start (k := 9) (m₀ := 12) (m := m)
      (by omega) (by omega) hle hineq0
    exact exists_large_prime_factor_of_choose_gt_pow_prime_count (m := m) (k := 9)
      (by omega) hm hineq
  · have hlt : m < 12 := Nat.lt_of_not_ge hle
    interval_cases m
    · exact ⟨11, 11, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨11, 11, by norm_num, by norm_num, by norm_num, by norm_num⟩

