import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

theorem sylvester_schur_of_fourth_lt_cube
    (n i : ℕ) (hi : 2500 ≤ i) (hi_half : i ≤ n / 2)
    (hlarge : i ^ 4 < n ^ 3) :
    ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i := by
  exact sylvester_schur_of_fourth_prime_count_bound n i (by omega) hi_half
    (primesBelow_succ_card_le_fourth hi) hlarge

