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

theorem unbounded_of_infinite (h : {p : ℕ | IsWilsonPrime p}.Infinite) :
    ∀ N : ℕ, ∃ p, N < p ∧ IsWilsonPrime p := by
  intro N
  obtain ⟨p, hp, hlt⟩ := h.exists_gt N
  exact ⟨p, hlt, hp⟩

/-- The infinitude conjecture is *equivalent* to the unboundedness statement. -/
