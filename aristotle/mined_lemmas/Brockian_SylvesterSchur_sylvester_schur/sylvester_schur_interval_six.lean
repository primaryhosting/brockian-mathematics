import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma sylvester_schur_interval_six {m : ℕ} (hm : 6 < m) :
    ∃ j p : ℕ, j ∈ Set.Ico m (m + 6) ∧ p.Prime ∧ 6 < p ∧ p ∣ j := by
  by_cases hle : 9 ≤ m
  · have hineq0 : (9 + 6 - 1) ^ (6 + 1).primesBelow.card < Nat.choose (9 + 6 - 1) 6 := by
      decide
    have hineq := choose_inequality_of_ge_start (k := 6) (m₀ := 9) (m := m)
      (by omega) (by omega) hle hineq0
    exact exists_large_prime_factor_of_choose_gt_pow_prime_count (m := m) (k := 6)
      (by omega) hm hineq
  · have hlt : m < 9 := Nat.lt_of_not_ge hle
    interval_cases m
    · exact ⟨7, 7, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨11, 11, by norm_num, by norm_num, by norm_num, by norm_num⟩

