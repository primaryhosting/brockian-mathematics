import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma sylvester_schur_interval_ten {m : ℕ} (hm : 10 < m) :
    ∃ j p : ℕ, j ∈ Set.Ico m (m + 10) ∧ p.Prime ∧ 10 < p ∧ p ∣ j := by
  have hineq0 : (11 + 10 - 1) ^ (10 + 1).primesBelow.card < Nat.choose (11 + 10 - 1) 10 := by
    decide
  have hineq := choose_inequality_of_ge_start (k := 10) (m₀ := 11) (m := m)
    (by omega) (by omega) (by omega) hineq0
  exact exists_large_prime_factor_of_choose_gt_pow_prime_count (m := m) (k := 10)
    (by omega) hm hineq

