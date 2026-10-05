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

/-!
# Wilson Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.WilsonPrimes.WilsonPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped Nat

namespace Brockian.WilsonPrimes

/-- A *Wilson prime* is a prime `p` with `p ^ 2 ∣ (p - 1)! + 1`
(the ordinary Wilson congruence `p ∣ (p-1)! + 1` holds for every prime). -/

theorem wilsonPrimes_infinite_iff_wilsonQuotient :
    {p : ℕ | IsWilsonPrime p}.Infinite ↔
      ∀ N : ℕ, ∃ p : ℕ, N < p ∧ p.Prime ∧ p ∣ wilsonQuotient p := by
  rw [wilsonPrimes_infinite_iff_unbounded]
  constructor
  · intro h N
    obtain ⟨p, hNp, hp⟩ := h N
    exact ⟨p, hNp, hp.1, (isWilsonPrime_iff_dvd_wilsonQuotient hp.1).1 hp⟩
  · intro h N
    obtain ⟨p, hNp, hp, hdvd⟩ := h N
    exact ⟨p, hNp, (isWilsonPrime_iff_dvd_wilsonQuotient hp).2 hdvd⟩

end Brockian.WilsonPrimes

