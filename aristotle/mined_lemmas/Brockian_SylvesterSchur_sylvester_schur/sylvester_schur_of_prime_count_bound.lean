import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

theorem sylvester_schur_of_prime_count_bound
    (n i r : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2)
    (hr_count : (i + 1).primesBelow.card ≤ r)
    (hlarge : i.factorial * n ^ r < (n - i + 1) ^ i) :
    ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i := by
  have hi_pos : 0 < i := hi
  have hi_le_n : i ≤ n := le_trans hi_half (Nat.div_le_self n 2)
  have hn_pos : 0 < n := by omega
  have hm : i < n - i + 1 := by omega
  have hN_eq : n - i + 1 + i - 1 = n := by omega
  have hlarge' :
      i.factorial * (n - i + 1 + i - 1) ^ r < (n - i + 1) ^ i := by
    simpa [hN_eq] using hlarge
  have hineq_m := choose_inequality_of_prime_count_bound (m := n - i + 1) (k := i) (r := r)
    hi_pos hm hr_count hlarge'
  have hineq :
      n ^ (i + 1).primesBelow.card < Nat.choose n i := by
    simpa [hN_eq] using hineq_m
  exact exists_large_prime_factor_of_choose_gt_pow_prime_count_direct hi_le_n hn_pos hineq

