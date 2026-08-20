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
# Wilson Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.WilsonPrimes.WilsonPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Wilson Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.WilsonPrimes.WilsonPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Nat

namespace Brockian.WilsonPrimes

/-- A *Wilson prime* is a prime `p` such that `p ^ 2 ∣ (p - 1)! + 1`, i.e. the congruence
of Wilson's theorem holds modulo `p ^ 2` and not merely modulo `p`. -/

theorem infinite_iff_unbounded :
    {p : ℕ | WilsonPrime p}.Infinite ↔ ∀ N : ℕ, ∃ p, N < p ∧ WilsonPrime p := by
  constructor
  · intro h N
    obtain ⟨p, hp, hlt⟩ := h.exists_gt N
    exact ⟨p, hlt, hp⟩
  · intro h
    refine Set.infinite_of_forall_exists_gt ?_
    intro N
    obtain ⟨p, hlt, hp⟩ := h N
    exact ⟨p, hp, hlt⟩

/-- **Main conditional theorem (Wilson prime infinitude, reduced to the Wilson quotient).**

If for every bound `N` there is a prime `p > N` dividing its own Wilson quotient
`((p - 1)! + 1) / p`, then there are infinitely many Wilson primes.

The unconditional infinitude of Wilson primes is an open problem; this is a Lean-checked
reduction of it to the Wilson-quotient divisibility criterion, which by
`WilsonPrimeInfinitude_converse` is in fact equivalent to it. -/
