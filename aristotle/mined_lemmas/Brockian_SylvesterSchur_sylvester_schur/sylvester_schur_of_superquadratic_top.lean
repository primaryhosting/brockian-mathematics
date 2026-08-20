import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

theorem sylvester_schur_of_superquadratic_top
    (n i : ℕ) (hi : 8 ≤ i) (hi_half : i ≤ n / 2) (hlarge : i ^ 2 < n) :
    ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i := by
  exact sylvester_schur_of_power_gap n i (i / 2) (by omega) hi_half
    (primesBelow_succ_card_le_half hi)
    (pow_mul_pow_half_lt_pow_of_sq_lt (by omega) hlarge)

