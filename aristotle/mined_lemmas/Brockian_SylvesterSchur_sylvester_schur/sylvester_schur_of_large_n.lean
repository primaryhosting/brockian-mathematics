import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

theorem sylvester_schur_of_large_n {n i : ℕ} (hi : 1 < i) (hi_half : i ≤ n / 2)
    (hlarge : i.factorial * 2 ^ (i - 1) < n - i + 1) :
    ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i := by
  let m := n - i + 1
  have hi_one : 1 ≤ i := by omega
  have hi_le_n : i ≤ n := le_trans hi_half (Nat.div_le_self n 2)
  have hm_pos : 0 < m := by
    dsimp [m]
    omega
  have hn_le : n ≤ 2 * m := by
    dsimp [m]
    omega
  have hlarge' : i.factorial * n ^ (i - 1) < m ^ i := by
    calc
      i.factorial * n ^ (i - 1) ≤ i.factorial * (2 * m) ^ (i - 1) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hn_le (i - 1))
      _ = (i.factorial * 2 ^ (i - 1)) * m ^ (i - 1) := by
        rw [mul_pow]
        ring
      _ < m * m ^ (i - 1) :=
        Nat.mul_lt_mul_of_pos_right hlarge (Nat.pow_pos (a := m) (n := i - 1) hm_pos)
      _ = m ^ (i - 1 + 1) := by
        rw [pow_succ]
        ring
      _ = m ^ i := by
        rw [Nat.sub_add_cancel hi_one]
  exact sylvester_schur_of_prime_count_bound n i (i - 1) hi_one hi_half
    (primesBelow_succ_card_le_pred i) (by simpa [m] using hlarge')

