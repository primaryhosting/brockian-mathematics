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
