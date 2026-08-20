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

theorem count_unbounded_of_sophieGermainPrimes_infinite
    (h : sophieGermainPrimes.Infinite) (C : ℕ) : ∃ N : ℕ, C < sophieGermainCount N := by
  obtain ⟨t, hts, htcard⟩ := h.exists_subset_card_eq (C + 1)
  refine ⟨t.sup id, ?_⟩
  have hsub : t ⊆ (Finset.range (t.sup id + 1)).filter IsSophieGermainPrime := by
    intro x hx
    have hx' : x ≤ t.sup id := Finset.le_sup (f := id) hx
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hts hx⟩
  have := Finset.card_le_card hsub
  simp only [sophieGermainCount]
  omega

/-- The counting-function criterion, as an equivalence. -/
