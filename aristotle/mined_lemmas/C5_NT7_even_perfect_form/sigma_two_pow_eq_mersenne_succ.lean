import Mathlib
namespace C5.NT7

open ArithmeticFunction Finset

open scoped sigma

/-- `σ 1 (2 ^ k) = 2 ^ (k + 1) - 1`, i.e. the sum of divisors of a power of two is the
corresponding Mersenne number. -/

private theorem sigma_two_pow_eq_mersenne_succ (k : ℕ) : σ 1 (2 ^ k) = mersenne (k + 1) := by
  simp_rw [sigma_one_apply, mersenne, ← one_add_one_eq_two, ← geom_sum_mul_add 1 (k + 1)]
  norm_num

/-- Every positive natural number is a power of two times an odd number. -/
