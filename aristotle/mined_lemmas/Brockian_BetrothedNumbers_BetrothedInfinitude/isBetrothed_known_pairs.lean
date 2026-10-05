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

import Mathlib
/-!
# Betrothed Infinitude
Category: Brockian Conjecture
Target: Brockian.BetrothedNumbers.BetrothedInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian
namespace BetrothedNumbers

open ArithmeticFunction

/-- `IsBetrothed m n` says that `(m, n)` is a *betrothed* (quasi-amicable) pair:
`0 < m < n` and the sum of the divisors of each of `m` and `n`, excluding the number
itself and `1`, equals the other number.  Equivalently `σ m = σ n = m + n + 1`. -/

theorem isBetrothed_known_pairs :
    ∀ p ∈ [(48, 75), (140, 195), (1050, 1925), (1575, 1648), (2024, 2295), (5775, 6128),
      (8892, 16587)], IsBetrothed p.1 p.2 := by
  decide

/-- In a betrothed pair the larger member is determined by the smaller one. -/
