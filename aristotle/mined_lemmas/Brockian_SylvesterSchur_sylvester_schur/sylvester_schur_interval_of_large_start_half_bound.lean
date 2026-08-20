import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

theorem sylvester_schur_interval_of_large_start_half_bound {m k : ℕ} (hk : 2 < k)
    (hm : k < m)
    (hlarge : k.factorial * 2 ^ (k / 2 + 1) < m ^ (k - (k / 2 + 1))) :
    ∃ j p : ℕ, j ∈ Set.Ico m (m + k) ∧ p.Prime ∧ k < p ∧ p ∣ j := by
  exact exists_large_prime_factor_of_choose_gt_pow_prime_count (m := m) (k := k)
    (by omega) hm (choose_inequality_of_large_start_half_bound hk hm hlarge)

