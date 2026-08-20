import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

theorem sylvester_schur_of_quadratic_large
    (n i : ℕ) (hi : 8 ≤ i) (hi_half : i ≤ n / 2)
    (hm_large : 4 * i ^ 2 ≤ n - i + 1) :
    ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i := by
  exact sylvester_schur_of_half_prime_count_bound n i hi hi_half
    (factorial_mul_pow_half_lt_of_quadratic_large hi hi_half hm_large)

