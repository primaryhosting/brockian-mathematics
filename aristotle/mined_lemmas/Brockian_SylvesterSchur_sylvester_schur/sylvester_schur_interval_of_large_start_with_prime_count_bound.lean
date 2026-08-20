import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

theorem sylvester_schur_interval_of_large_start_with_prime_count_bound {m k r : ℕ}
    (hm : k < m)
    (hr_count : (k + 1).primesBelow.card ≤ r) (hrk : r < k)
    (hlarge : k.factorial * 2 ^ r < m ^ (k - r)) :
    ∃ j p : ℕ, j ∈ Set.Ico m (m + k) ∧ p.Prime ∧ k < p ∧ p ∣ j := by
  exact exists_large_prime_factor_of_choose_gt_pow_prime_count (m := m) (k := k)
    (by omega) hm
    (choose_inequality_of_large_start_with_prime_count_bound hm hr_count hrk hlarge)

