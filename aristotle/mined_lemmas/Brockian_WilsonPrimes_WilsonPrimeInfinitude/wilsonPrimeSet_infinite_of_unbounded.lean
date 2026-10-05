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
# Wilson Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.WilsonPrimes.WilsonPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.WilsonPrimes

open Nat

/-- A *Wilson prime* is a prime `p` such that `p ^ 2` divides `(p - 1)! + 1`.
By Wilson's theorem, every prime `p` satisfies `p ∣ (p - 1)! + 1`; a Wilson prime
is one for which the stronger, squared divisibility holds. -/

theorem wilsonPrimeSet_infinite_of_unbounded
    (h : ∀ N : ℕ, ∃ p, N < p ∧ p.Prime ∧ p ^ 2 ∣ (p - 1)! + 1) :
    wilsonPrimeSet.Infinite :=
  WilsonPrimeInfinitude.mp fun N => by
    obtain ⟨p, hp, hp1, hp2⟩ := h N
    exact ⟨p, hp, hp1, hp2⟩

end Brockian.WilsonPrimes

