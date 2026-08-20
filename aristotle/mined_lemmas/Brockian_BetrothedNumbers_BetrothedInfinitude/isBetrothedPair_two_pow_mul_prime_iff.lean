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

theorem isBetrothedPair_two_pow_mul_prime_iff {k p : ℕ} (hk : 1 ≤ k) (hp : p.Prime) (hp2 : p ≠ 2) :
    (∃ m, IsBetrothedPair m (2 ^ k * p)) ↔
      σ 1 ((2 ^ k - 1) * (p + 2)) = (2 ^ (k + 1) - 1) * (p + 1) := by
  constructor
  · rintro ⟨m, hm⟩
    have hme : m = (2 ^ k - 1) * (p + 2) := eq_of_isBetrothedPair_two_pow_mul_prime hp hp2 hm
    obtain ⟨-, -, -, h1, -⟩ := hm
    have key := sigma_criterion_key k p
    rw [hme] at h1
    omega
  · intro h
    exact ⟨_, betrothed_of_sigma_criterion hk hp hp2 h⟩

/-! ### Concrete betrothed pairs -/

/-- `(48, 75)` is a betrothed pair: `σ 48 = σ 75 = 124 = 48 + 75 + 1`. -/
