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

-- # Sophie Germain Infinitude
-- Category: Brockian Conjecture
-- Target: Brockian.SophieGermain.SophieGermainInfinitude
-- Verification: pending
-- Provenance: Aristotle theorem prover (Harmonic)

import Mathlib

/-!
# Sophie Germain Infinitude
Category: Brockian Conjecture
Target: Brockian.SophieGermain.SophieGermainInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxRecDepth 40000

namespace Brockian.SophieGermain

/-- A *Sophie Germain prime* is a prime `p` such that `2 * p + 1` is also prime. -/

theorem safePrime_infinite_iff : safePrimeSet.Infinite ↔ sophieGermainSet.Infinite := by
  constructor
  · intro h
    rw [infinite_iff_unbounded]
    intro N
    obtain ⟨q, hq, hqN⟩ := h.exists_gt (2 * N + 1)
    obtain ⟨p, hp, rfl⟩ := hq
    exact ⟨p, by omega, hp⟩
  · intro h
    have himg : safePrimeSet = (fun p => 2 * p + 1) '' sophieGermainSet := by
      ext q
      constructor
      · rintro ⟨p, hp, rfl⟩; exact ⟨p, hp, rfl⟩
      · rintro ⟨p, hp, rfl⟩; exact ⟨p, hp, rfl⟩
    rw [himg]
    exact h.image (Set.injOn_of_injective (fun a b hab => by omega))

/-- **Sophie Germain infinitude (conditional reduction).**

The infinitude of Sophie Germain primes — an open problem — is here established
*conditionally*: it follows from (and is in fact equivalent to) either of the two
standard reformulations, namely unboundedness of the set of Sophie Germain primes,
or infinitude of the set of safe primes.  The statement also records the
unconditional fact that Sophie Germain primes exist. -/
