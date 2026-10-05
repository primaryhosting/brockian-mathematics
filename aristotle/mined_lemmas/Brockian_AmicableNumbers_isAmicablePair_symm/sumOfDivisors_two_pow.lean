import Mathlib

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-
# Amicable Infinitude
Category: Brockian Conjecture
Target: Brockian.AmicableNumbers.AmicableInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Amicable Infinitude
Category: Brockian Conjecture
Target: Brockian.AmicableNumbers.AmicableInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.AmicableNumbers

open Finset ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-- The sum of all (positive) divisors of `n`.  For `n = 0` this is `0`. -/

theorem sumOfDivisors_two_pow (n : ℕ) : sumOfDivisors (2 ^ n) + 1 = 2 ^ (n + 1) := by
  rw [sumOfDivisors, ← sigma_one_apply, sigma_one_apply_prime_pow Nat.prime_two]
  induction n with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ]; ring_nf; ring_nf at ih; omega

/-! ### The rule of Thâbit ibn Qurra -/

/-- The integer identity underlying Thâbit ibn Qurra's rule: with
`A = 2 ^ (k+3) - 1`, `P = 3 * 2 ^ (k+1) - 1`, `Q = 3 * 2 ^ (k+2) - 1` and
`R = 9 * 2 ^ (2k+3) - 1`, both `A * (P+1) * (Q+1)` and `A * (R+1)` equal
`2 ^ (k+2) * P * Q + 2 ^ (k+2) * R`. -/
