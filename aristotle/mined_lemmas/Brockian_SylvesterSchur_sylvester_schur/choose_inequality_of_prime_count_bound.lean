import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma choose_inequality_of_prime_count_bound {m k r : ℕ}
    (hk : 0 < k) (hm : k < m)
    (hr_count : (k + 1).primesBelow.card ≤ r)
    (hlarge : k.factorial * (m + k - 1) ^ r < m ^ k) :
    (m + k - 1) ^ (k + 1).primesBelow.card < Nat.choose (m + k - 1) k := by
  let s := (k + 1).primesBelow.card
  have hm_pos : 0 < m := by omega
  have hN_pos : 0 < m + k - 1 := by omega
  have hpow_le : (m + k - 1) ^ s ≤ (m + k - 1) ^ r :=
    Nat.pow_le_pow_right hN_pos (by simpa [s] using hr_count)
  have hchoose_eq := ascFactorial_eq_factorial_mul_choose_start (m := m) (k := k) hm_pos
  have hmul_lt_choose :
      k.factorial * (m + k - 1) ^ s < k.factorial * Nat.choose (m + k - 1) k := by
    calc
      k.factorial * (m + k - 1) ^ s ≤ k.factorial * (m + k - 1) ^ r :=
        Nat.mul_le_mul_left _ hpow_le
      _ < m ^ k := hlarge
      _ ≤ m.ascFactorial k := pow_le_ascFactorial m k
      _ = k.factorial * Nat.choose (m + k - 1) k := hchoose_eq
  exact Nat.lt_of_mul_lt_mul_left hmul_lt_choose

