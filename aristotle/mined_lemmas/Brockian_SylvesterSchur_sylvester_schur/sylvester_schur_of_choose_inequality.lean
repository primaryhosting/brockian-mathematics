import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

theorem sylvester_schur_of_choose_inequality
    (hineq : ∀ ⦃n i : ℕ⦄, 1 ≤ i → i ≤ n / 2 →
      n ^ (i + 1).primesBelow.card < Nat.choose n i)
    (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2) :
    ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i := by
  have hi_le_n : i ≤ n := le_trans hi_half (Nat.div_le_self n 2)
  have hn_pos : 0 < n := by omega
  exact exists_large_prime_factor_of_choose_gt_pow_prime_count_direct hi_le_n hn_pos
    (hineq hi hi_half)

