import Mathlib

namespace Brockian.EvenPerfectMod9

open ArithmeticFunction Finset
open scoped sigma

/-- The sum of the divisors of a power of two is the corresponding Mersenne number.
This is a main-library reconstruction of the ingredient needed for Euclid--Euler. -/

theorem sigma_two_pow_eq_mersenne_succ_main (k : ℕ) :
    σ 1 (2 ^ k) = mersenne (k + 1) := by
  simp_rw [sigma_one_apply, mersenne, ← one_add_one_eq_two,
    ← geom_sum_mul_add 1 (k + 1)]
  norm_num

/-- Every positive natural number is a power of two times an odd number. -/
