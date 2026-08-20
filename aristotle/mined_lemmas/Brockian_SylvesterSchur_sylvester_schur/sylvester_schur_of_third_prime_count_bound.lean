import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

theorem sylvester_schur_of_third_prime_count_bound
    (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2)
    (hr_count : (i + 1).primesBelow.card ≤ i / 3)
    (hlarge : i ^ 3 < n ^ 2) :
    ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i := by
  exact sylvester_schur_of_power_gap n i (i / 3) hi hi_half hr_count
    (pow_mul_pow_third_lt_pow_of_cube_lt_sq (by omega) (by omega) hlarge)

