import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma choose_inequality_of_large_start {m k : ℕ} (hk : 1 < k) (hm : k < m)
    (hlarge : k.factorial * 2 ^ (k - 1) < m) :
    (m + k - 1) ^ (k + 1).primesBelow.card < Nat.choose (m + k - 1) k := by
  have hlarge' : k.factorial * 2 ^ (k - 1) < m ^ (k - (k - 1)) := by
    simpa [show k - (k - 1) = 1 by omega] using hlarge
  exact choose_inequality_of_large_start_with_prime_count_bound (m := m) (k := k) (r := k - 1)
    hm (primesBelow_succ_card_le_pred k) (by omega) hlarge'

