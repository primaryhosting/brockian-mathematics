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

theorem goldbach_le_hundred (n : ℕ) (hle : n ≤ 100) (he : Even n) (h4 : 4 ≤ n) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = n := by
  have key : ∀ m ∈ Finset.range 101, Even m → 4 ≤ m →
      ∃ p ∈ Finset.range 101, ∃ q ∈ Finset.range 101, Nat.Prime p ∧ Nat.Prime q ∧ p + q = m := by
    decide
  obtain ⟨p, -, q, -, hp, hq, hpq⟩ := key n (Finset.mem_range.2 (by omega)) he h4
  exact ⟨p, q, hp, hq, hpq⟩

/-- The spectral model is unconditionally positive at every even level `4 ≤ n ≤ 100`. -/
