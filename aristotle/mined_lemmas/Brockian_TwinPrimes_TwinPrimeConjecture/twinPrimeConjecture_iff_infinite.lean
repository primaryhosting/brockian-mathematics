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
# Twin Prime Conjecture
Category: Brockian Conjecture
Target: Brockian.TwinPrimes.TwinPrimeConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped Nat

namespace Brockian.TwinPrimes

/-- **The Twin Prime Conjecture**: there are arbitrarily large primes `p` such that
`p + 2` is also prime. -/

theorem twinPrimeConjecture_iff_infinite : TwinPrimeConjecture ↔ twinPrimes.Infinite := by
  constructor
  · intro h
    refine Set.infinite_of_forall_exists_gt ?_
    intro a
    obtain ⟨p, hp, hp1, hp2⟩ := h a
    exact ⟨p, Set.mem_setOf_eq ▸ ⟨hp1, hp2⟩, hp⟩
  · intro h n
    obtain ⟨p, hp, hpn⟩ := h.exists_gt n
    exact ⟨p, hpn, hp.1, hp.2⟩

/-- Contrapositive form: the twin prime conjecture fails exactly when some bound `N`
cuts off all twin primes. -/
