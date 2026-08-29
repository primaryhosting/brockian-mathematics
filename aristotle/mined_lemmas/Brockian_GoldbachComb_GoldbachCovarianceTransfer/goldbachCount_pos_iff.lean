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
# Goldbach Covariance Transfer
Category: Brockian Conjecture
Target: Brockian.GoldbachComb.GoldbachCovarianceTransfer
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators Classical

namespace Brockian.GoldbachComb

/-- `n` is Goldbach representable if it is a sum of two primes. -/

lemma goldbachCount_pos_iff (n : ℕ) : 0 < goldbachCount n ↔ Representable n := by
  constructor
  · intro h
    rw [goldbachCount, Finset.card_pos] at h
    obtain ⟨p, hp⟩ := h
    rw [Finset.mem_filter, Finset.mem_range] at hp
    exact ⟨p, n - p, hp.2.1, hp.2.2, by omega⟩
  · rintro ⟨p, q, hp, hq, rfl⟩
    rw [goldbachCount, Finset.card_pos]
    refine ⟨p, ?_⟩
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, hp, ?_⟩
    simpa using hq

/-- Pointwise, multiplying the representation count by the Goldbach indicator changes nothing. -/
