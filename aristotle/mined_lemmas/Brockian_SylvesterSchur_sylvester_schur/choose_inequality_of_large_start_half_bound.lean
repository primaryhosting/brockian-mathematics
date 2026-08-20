import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma choose_inequality_of_large_start_half_bound {m k : ℕ} (hk : 2 < k) (hm : k < m)
    (hlarge : k.factorial * 2 ^ (k / 2 + 1) < m ^ (k - (k / 2 + 1))) :
    (m + k - 1) ^ (k + 1).primesBelow.card < Nat.choose (m + k - 1) k := by
  exact choose_inequality_of_large_start_with_prime_count_bound (m := m) (k := k)
    (r := k / 2 + 1) hm (primesBelow_succ_card_le_half_add_one k) (by omega) hlarge

