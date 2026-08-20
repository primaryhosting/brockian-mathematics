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
# Betrothed Infinitude
Category: Brockian Conjecture
Target: Brockian.BetrothedNumbers.BetrothedInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Betrothed Infinitude
Category: Brockian Conjecture
Target: Brockian.BetrothedNumbers.BetrothedInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace Brockian.BetrothedNumbers

/-- Two positive integers `m ≠ n` form a *betrothed* (or *quasi-amicable*) pair when the sum of
the divisors of each, excluding `1` and the number itself, equals the other number; equivalently
`σ m = σ n = m + n + 1`. -/

theorem eq_of_isBetrothedPair_two_pow_mul_prime {k p m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : IsBetrothedPair m (2 ^ k * p)) : m = (2 ^ k - 1) * (p + 2) := by
  obtain ⟨-, -, -, -, h2⟩ := h
  rw [sigma_one_two_pow_mul_prime hp hp2] at h2
  have key := sigma_criterion_key k p
  omega

/-- For `n = 2 ^ k * p` with `k ≥ 1` and `p` an odd prime, `n` belongs to a betrothed pair exactly
when the Thabit-style criterion holds. -/
