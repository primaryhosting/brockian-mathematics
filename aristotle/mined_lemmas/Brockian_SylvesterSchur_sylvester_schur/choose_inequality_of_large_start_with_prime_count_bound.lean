import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma choose_inequality_of_large_start_with_prime_count_bound {m k r : ℕ}
    (hm : k < m)
    (hr_count : (k + 1).primesBelow.card ≤ r) (hrk : r < k)
    (hlarge : k.factorial * 2 ^ r < m ^ (k - r)) :
    (m + k - 1) ^ (k + 1).primesBelow.card < Nat.choose (m + k - 1) k := by
  have hm_pos : 0 < m := by omega
  have hN_le : m + k - 1 ≤ 2 * m := by omega
  have hlarge' : k.factorial * (m + k - 1) ^ r < m ^ k := by
    calc
      k.factorial * (m + k - 1) ^ r ≤ k.factorial * (2 * m) ^ r :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hN_le r)
      _ = (k.factorial * 2 ^ r) * m ^ r := by
          rw [mul_pow]
          ring
      _ < m ^ (k - r) * m ^ r :=
        Nat.mul_lt_mul_of_pos_right hlarge (Nat.pow_pos (a := m) (n := r) hm_pos)
      _ = m ^ k := by
        rw [← pow_add]
        congr 1
        omega
  exact choose_inequality_of_prime_count_bound (by omega) hm hr_count hlarge'

