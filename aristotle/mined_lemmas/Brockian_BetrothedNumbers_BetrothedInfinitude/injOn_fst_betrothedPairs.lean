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

namespace Brockian.BetrothedNumbers

/-- The sum-of-divisors function `σ₁ n = ∑_{d ∣ n} d` (with the convention `σ₁ 0 = 0`). -/

theorem injOn_fst_betrothedPairs : Set.InjOn Prod.fst betrothedPairs := by
  rintro ⟨m, n⟩ hp ⟨m', n'⟩ hq (hmm : m = m')
  subst hmm
  simpa using betrothed_partner_unique hp hq

/--
**Betrothed Infinitude.**

There are infinitely many betrothed (quasi-amicable) pairs if and only if the first members
of such pairs are unbounded, i.e. for every `N` there is a betrothed pair whose first member
exceeds `N`.

(Whether either side actually holds is an open problem; this is the unconditional equivalence
of the two standard formulations of the conjecture.)
-/
