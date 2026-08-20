import Mathlib
import PerfectNumbersEuler

namespace Brockian.EvenPerfectMod9

open Nat

/-- The modular-arithmetic consequence of the Euclid–Euler form of an even perfect number. -/

theorem sigma_two_pow_eq_mersenne_succ (k : ℕ) : σ 1 (2 ^ k) = mersenne (k + 1) := by
  simp_rw [sigma_one_apply, mersenne, ← one_add_one_eq_two, ← geom_sum_mul_add 1 (k + 1)]
  norm_num

/-- Euclid's theorem that Mersenne primes induce perfect numbers -/
