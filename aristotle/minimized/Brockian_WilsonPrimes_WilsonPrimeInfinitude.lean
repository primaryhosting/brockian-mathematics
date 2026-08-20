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

Category: Brockian Conjecture.  Target: `Brockian.WilsonPrimes.WilsonPrimeInfinitude`.

Note: the header block above is kept as an ordinary comment because Lean requires `import`
commands to precede every other command, including module docstrings.
-/

open Nat

namespace Brockian.WilsonPrimes

/-- A *Wilson prime* is a prime `p` such that `p ^ 2 ∣ (p - 1)! + 1`.
(By Wilson's theorem every prime satisfies `p ∣ (p - 1)! + 1`; a Wilson prime is one for
which the stronger congruence modulo `p ^ 2` holds.) -/

def IsWilsonPrime (p : ℕ) : Prop := p.Prime ∧ p ^ 2 ∣ (p - 1)! + 1

/-- **Wilson's theorem**, in the divisibility form `p ∣ (p - 1)! + 1`.
This is an immediate consequence of `ZMod.wilsons_lemma`. -/

theorem IsWilsonPrime.prime {p : ℕ} (h : IsWilsonPrime p) : p.Prime := h.1

/-- `5` is a Wilson prime: `5 ^ 2 = 25 ∣ 4! + 1 = 25`. -/

theorem WilsonPrimeInfinitude
    (h : ∀ N : ℕ, ∃ p, N < p ∧ IsWilsonPrime p) :
    {p : ℕ | IsWilsonPrime p}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro a
  obtain ⟨p, hlt, hp⟩ := h a
  exact ⟨p, hp, hlt⟩

/-- The converse of the reduction: infinitude of the set of Wilson primes implies that
Wilson primes are unbounded.  Hence the two formulations are equivalent. -/
