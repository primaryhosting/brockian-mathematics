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

open Finset

/-- The sum-of-divisors function `σ₁ n = ∑_{d ∣ n} d`. -/

theorem injOn_fst_betrothedSet : Set.InjOn Prod.fst betrothedSet := by
  rintro ⟨m, n⟩ hp ⟨m', n'⟩ hq hmm
  simp only [betrothedSet, Set.mem_setOf_eq] at hp hq
  simp only at hmm
  exact Prod.ext hmm (eq_of_fst_eq hp hq hmm)

/-!
## Main statement

Whether there are infinitely many betrothed (quasi-amicable) pairs is an open
problem.  What we prove here is the exact *reduction* of infinitude to
unboundedness: the set of betrothed pairs is infinite if and only if the first
members of betrothed pairs are unbounded.  Both directions are unconditional
theorems; the conjecture itself is the (unproved) right-hand side.
-/

/-- **Betrothed infinitude, as a reduction.**
The set of betrothed pairs is infinite iff for every bound `N` there is a
betrothed pair `(m, n)` with `N < m`. -/
