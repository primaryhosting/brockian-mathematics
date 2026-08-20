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

theorem sigma_one_nine : ArithmeticFunction.sigma 1 9 = 13 := by
  have h := sigma_one_apply_prime_pow (p := 3) (i := 2) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  simpa using h

/-- `sigma_1(5) = 6`. -/
