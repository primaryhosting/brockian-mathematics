import Mathlib

/-!
# Sigma 5040
Category: Riemann Program
Target: Riemann.Robin.sigma_5040
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Riemann.Robin

open ArithmeticFunction

/-- `sigma_1(2^4) = 1 + 2 + 4 + 8 + 16 = 31`, via
`ArithmeticFunction.sigma_one_apply_prime_pow`. -/
theorem sigma_one_sixteen : ArithmeticFunction.sigma 1 16 = 31 := by
  have h := sigma_one_apply_prime_pow (p := 2) (i := 4) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  simpa using h

/-- `sigma_1(3^2) = 1 + 3 + 9 = 13`. -/
theorem sigma_one_nine : ArithmeticFunction.sigma 1 9 = 13 := by
  have h := sigma_one_apply_prime_pow (p := 3) (i := 2) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  simpa using h

/-- `sigma_1(5) = 6`. -/
theorem sigma_one_five : ArithmeticFunction.sigma 1 5 = 6 := by
  have h := sigma_one_apply_prime_pow (p := 5) (i := 1) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  simpa using h

/-- `sigma_1(7) = 8`. -/
theorem sigma_one_seven : ArithmeticFunction.sigma 1 7 = 8 := by
  have h := sigma_one_apply_prime_pow (p := 7) (i := 1) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  simpa using h

/-- The sum of divisors of `5040 = 2^4 * 3^2 * 5 * 7` is `19344 = 31 * 13 * 6 * 8`.

`5040` is the largest known exception to Robin's inequality
`σ(n) < e^γ · n · log log n`, whose validity for all `n > 5040` is equivalent to
the Riemann hypothesis.

The proof uses multiplicativity of `σ` (`ArithmeticFunction.isMultiplicative_sigma`)
together with the prime-power formula
`ArithmeticFunction.sigma_one_apply_prime_pow`. -/
theorem sigma_5040 : ArithmeticFunction.sigma 1 5040 = 19344 := by
  have m : IsMultiplicative (ArithmeticFunction.sigma 1) := isMultiplicative_sigma
  have e3 : ArithmeticFunction.sigma 1 (5 * 7) = 6 * 8 := by
    rw [m.map_mul_of_coprime (by norm_num), sigma_one_five, sigma_one_seven]
  have e2 : ArithmeticFunction.sigma 1 (9 * 35) = 13 * ArithmeticFunction.sigma 1 35 := by
    rw [m.map_mul_of_coprime (by norm_num), sigma_one_nine]
  have e1 : ArithmeticFunction.sigma 1 (16 * 315) = 31 * ArithmeticFunction.sigma 1 315 := by
    rw [m.map_mul_of_coprime (by norm_num), sigma_one_sixteen]
  norm_num at e1 e2 e3
  rw [show (5040 : ℕ) = 16 * 315 by norm_num, e1, show (315 : ℕ) = 9 * 35 by norm_num, e2, e3]

end Riemann.Robin

