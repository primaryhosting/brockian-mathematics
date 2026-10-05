import Mathlib

/-!
# Betrothed 5775 6128
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.betrothed_5775_6128
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.BetrothedNumbers

open ArithmeticFunction

/-- Two distinct positive naturals `m ≠ n` form a *betrothed* (quasi-amicable) pair when
each one's sum of divisors equals `m + n + 1`; equivalently, the sum of the divisors of
each, excluding `1` and the number itself, equals the other number. -/

theorem betrothed_5775_6128_criterion_data :
    Nat.Prime 383 ∧ (383 : ℕ) ≠ 2 ∧ 2 ^ 4 * 383 = 6128 ∧
      sigma 1 (2 ^ 4) * sigma 1 383 = 5775 + 6128 + 1 ∧
      IsBetrothedPair 5775 (2 ^ 4 * 383) := by
  refine ⟨prime_383, by norm_num, by norm_num, ?_, betrothed_5775_6128_of_criterion⟩
  rw [sigma_one_two_pow, sigma_one_prime prime_383]
  norm_num

end Brockian.BetrothedNumbers

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

