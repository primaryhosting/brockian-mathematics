import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

theorem sylvester_schur_of_cube_lt_square
    (n i : ℕ) (hi : 49 ≤ i) (hi_half : i ≤ n / 2)
    (hlarge : i ^ 3 < n ^ 2) :
    ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i := by
  exact sylvester_schur_of_third_prime_count_bound n i (by omega) hi_half
    (primesBelow_succ_card_le_third hi) hlarge

