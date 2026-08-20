import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

theorem sylvester_schur_of_half_prime_count_bound
    (n i : ℕ) (hi : 8 ≤ i) (hi_half : i ≤ n / 2)
    (hlarge : i.factorial * n ^ (i / 2) < (n - i + 1) ^ i) :
    ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i := by
  exact sylvester_schur_of_prime_count_bound n i (i / 2) (by omega) hi_half
    (primesBelow_succ_card_le_half hi) hlarge

