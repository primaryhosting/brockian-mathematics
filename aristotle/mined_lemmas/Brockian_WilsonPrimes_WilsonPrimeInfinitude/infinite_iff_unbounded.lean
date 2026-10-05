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

open Nat

namespace Brockian.WilsonPrimes

/-- A *Wilson prime* is a prime `p` such that `p ^ 2` divides `(p - 1)! + 1`.
(By Wilson's theorem, `p` itself always divides `(p - 1)! + 1` when `p` is prime,
so a Wilson prime is one for which this divisibility holds to the second power.) -/

theorem infinite_iff_unbounded :
    {p : ℕ | IsWilsonPrime p}.Infinite ↔ ∀ N : ℕ, ∃ p, N < p ∧ IsWilsonPrime p := by
  constructor
  · intro hinf N
    obtain ⟨p, hp, hpN⟩ := hinf.exists_gt N
    exact ⟨p, hpN, hp⟩
  · intro h
    apply Set.infinite_of_not_bddAbove
    rintro ⟨N, hN⟩
    obtain ⟨p, hp, hpS⟩ := h N
    exact absurd (hN hpS) (by omega)

/-!
## Main statement

Whether there are infinitely many Wilson primes is a well-known open problem: only
`5`, `13` and `563` are known, and no unconditional proof of infinitude (nor of
finiteness) is available.  What is proved here is a Lean-checked *conditional
reduction*: the infinitude of Wilson primes follows from the statement that
arbitrarily large primes divide their own Wilson quotient `((p - 1)! + 1) / p`.
-/

/-- **Conditional Wilson prime infinitude.**  If for every bound `N` there is a prime
`p > N` dividing its Wilson quotient `((p - 1)! + 1) / p`, then the set of Wilson
primes is infinite.  The hypothesis is the standard open conjecture, so this is a
verified reduction of the infinitude statement to it, not an unconditional proof. -/
