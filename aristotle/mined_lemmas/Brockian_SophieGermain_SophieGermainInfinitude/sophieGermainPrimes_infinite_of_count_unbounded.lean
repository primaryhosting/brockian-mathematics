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

theorem sophieGermainPrimes_infinite_of_count_unbounded
    (h : ∀ C : ℕ, ∃ N : ℕ, C < sophieGermainCount N) : sophieGermainPrimes.Infinite := by
  intro hfin
  obtain ⟨N, hN⟩ := h hfin.toFinset.card
  have hsub : (Finset.range (N + 1)).filter IsSophieGermainPrime ⊆ hfin.toFinset := by
    intro x hx
    simp only [Finset.mem_filter] at hx
    exact hfin.mem_toFinset.2 hx.2
  exact absurd (Finset.card_le_card hsub) (by simpa [sophieGermainCount] using hN)

/-- Conversely, if there are infinitely many Sophie Germain primes then their counting
function is unbounded. -/
