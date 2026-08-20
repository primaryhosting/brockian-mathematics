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

Whether there are infinitely many amicable numbers is a well-known open problem.
This file gives a Lean-checked **conditional reduction**: if there are infinitely many
Thābit-type exponents `k` (i.e. `3·2^k - 1`, `3·2^(k+1) - 1` and `9·2^(2k+1) - 1` are all
prime), then there are infinitely many amicable numbers.  It also records the
unconditional partial result that amicable numbers exist (the pair `(220, 284)`).
-/

namespace Brockian.AmicableNumbers

open ArithmeticFunction

/-- The sum of the proper divisors of `n`. -/

theorem sigma_one_two_pow (k : ℕ) : sigma 1 (2 ^ k) + 1 = 2 ^ (k + 1) := by
  have h : sigma 1 (2 ^ k) = 2 ^ (k + 1) - 1 := by
    simp [sigma_one_apply, Nat.sum_divisors_prime_pow Nat.prime_two, Nat.geomSum_eq]
  have h2 : 1 ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
  omega

/-- **Thābit ibn Qurra's rule.**  If `p + 1 = 3·2^k`, `q + 1 = 3·2^(k+1)` and
`r + 1 = 9·2^(2k+1)` are all prime (`k ≥ 1`), then `2^(k+1)·p·q` and `2^(k+1)·r`
form an amicable pair. -/
