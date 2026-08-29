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
# Practical Twin Infinitude
Category: Brockian Conjecture
Target: Brockian.PracticalNumbers.PracticalTwinInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.PracticalNumbers

/-- A natural number `n` is *practical* if it is positive and every `t ≤ n` can be written
as a sum of distinct divisors of `n`. -/

theorem Reach.step {D : Finset ℕ} {B x : ℕ} (h : Reach D B) (hx : x ≤ B + 1)
    (hlt : ∀ y ∈ D, y < x) : Reach (insert x D) (B + x) := by
  intro t ht
  by_cases hcase : t ≤ B
  · obtain ⟨S, hS, hsum⟩ := h t hcase
    exact ⟨S, hS.trans (Finset.subset_insert _ _), hsum⟩
  · push_neg at hcase
    obtain ⟨S, hS, hsum⟩ := h (t - x) (by omega)
    have hxS : x ∉ S := fun hmem => absurd (hlt x (hS hmem)) (lt_irrefl x)
    refine ⟨insert x S, Finset.insert_subset_insert _ hS, ?_⟩
    rw [Finset.sum_insert hxS, hsum]
    omega

/-- Every divisor of a positive number is at most that number. -/
