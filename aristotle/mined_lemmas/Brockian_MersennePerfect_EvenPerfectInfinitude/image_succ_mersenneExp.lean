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
# Even Perfect Infinitude
Category: Brockian Conjecture
Target: Brockian.MersennePerfect.EvenPerfectInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian.MersennePerfect

open ArithmeticFunction Finset
open scoped sigma

/-- The set of even perfect numbers. -/

lemma image_succ_mersenneExp : (fun k => k + 1) '' MersenneExp = MersennePrimeExp := by
  ext p
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨Nat.Prime.of_mersenne hk, hk⟩
  · rintro ⟨hp, hmp⟩
    have hp1 : p - 1 + 1 = p := by have := hp.two_le; omega
    refine ⟨p - 1, ?_, by simpa using hp1⟩
    simpa [MersenneExp, hp1] using hmp

/-- Restatement of the reduction: there are infinitely many even perfect numbers iff there are
infinitely many Mersenne primes `2 ^ p - 1` (with `p` prime). -/
