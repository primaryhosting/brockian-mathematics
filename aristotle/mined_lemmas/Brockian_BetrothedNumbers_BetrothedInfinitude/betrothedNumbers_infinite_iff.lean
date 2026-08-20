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

theorem betrothedNumbers_infinite_iff :
    betrothedNumbers.Infinite ↔ ∀ N : ℕ, ∃ m ∈ betrothedNumbers, N < m := by
  constructor
  · intro h N
    obtain ⟨m, hm, hmN⟩ := h.exists_gt N
    exact ⟨m, hm, hmN⟩
  · exact Set.infinite_of_forall_exists_gt

/-- **Betrothed infinitude (conditional).**  Whether there are infinitely many betrothed
(quasi-amicable) pairs is an open problem.  The following is a Lean-checked reduction: if the
Thabit-style criterion `σ ((2 ^ k - 1) * (p + 2)) = (2 ^ (k + 1) - 1) * (p + 1)` has solutions
with `k ≥ 1`, `p` an odd prime and `(2 ^ k - 1) * (p + 2)` arbitrarily large, then there are
infinitely many betrothed numbers, hence infinitely many betrothed pairs. -/
