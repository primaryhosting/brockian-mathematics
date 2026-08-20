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
# Goldbach From Spectral Model
Category: Brockian (Open Discharge)
Target: Brockian.GoldbachSchema.goldbach_from_spectral_model
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat

namespace Brockian.GoldbachSchema

open Finset Complex

/-- The primes below `n`, i.e. the support of the spectral model at level `n`. -/

theorem goldbachCount_ne_zero_iff (n : ℕ) :
    goldbachCount n ≠ 0 ↔ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = n := by
  rw [goldbachCount, ← Nat.pos_iff_ne_zero, Finset.card_pos]
  constructor
  · rintro ⟨pq, hpq⟩
    simp only [primesBelow, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hpq
    exact ⟨pq.1, pq.2, hpq.1.1.2, hpq.1.2.2, hpq.2⟩
  · rintro ⟨p, q, hp, hq, rfl⟩
    refine ⟨(p, q), ?_⟩
    have := hp.two_le
    have := hq.two_le
    simp only [primesBelow, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    exact ⟨⟨⟨by omega, hp⟩, by omega, hq⟩, trivial⟩

/-- Faithfulness of the spectral model: at every level `n ≥ 1`, spectral positivity is
*equivalent* to the existence of a Goldbach representation of `n`. -/
