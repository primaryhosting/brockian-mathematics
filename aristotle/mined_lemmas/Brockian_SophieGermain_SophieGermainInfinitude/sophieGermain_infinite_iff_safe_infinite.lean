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
# Sophie Germain Infinitude
Category: Brockian Conjecture
Target: Brockian.SophieGermain.SophieGermainInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Sophie Germain Infinitude
Category: Brockian Conjecture
Target: Brockian.SophieGermain.SophieGermainInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.SophieGermain

/-- A *Sophie Germain prime* is a prime `p` such that `2 * p + 1` is also prime. -/

theorem sophieGermain_infinite_iff_safe_infinite :
    {p : ℕ | IsSophieGermainPrime p}.Infinite ↔ {q : ℕ | IsSafePrime q}.Infinite := by
  rw [infinite_iff_unbounded, infinite_iff_unbounded]
  constructor
  · intro h N
    obtain ⟨p, hp, hpN⟩ := h N
    exact ⟨2 * p + 1, ⟨hp.2, p, rfl, hp.1⟩, by omega⟩
  · intro h N
    obtain ⟨q, hq, hqN⟩ := h (2 * N + 1)
    obtain ⟨hqp, p, rfl, hp⟩ := hq
    exact ⟨p, ⟨hp, hqp⟩, by omega⟩

/-! ### The conditional reduction

The infinitude of Sophie Germain primes is a long-standing open problem, so the main
statement below is a *conditional* one: from the existence of arbitrarily large safe
primes we deduce that the set of Sophie Germain primes is infinite. -/

/-- **Sophie Germain infinitude, conditionally.** If there are arbitrarily large safe
primes (primes of the form `2 * p + 1` with `p` prime), then there are infinitely many
Sophie Germain primes. -/
