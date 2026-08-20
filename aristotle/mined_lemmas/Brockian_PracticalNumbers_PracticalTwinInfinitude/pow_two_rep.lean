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

open Finset

/-- A natural number `n` is *practical* if it is positive and every `m ≤ n` can be written
as a sum of distinct divisors of `n`. -/

lemma pow_two_rep (k : ℕ) :
    ∀ m < 2 ^ k, ∃ S ⊆ (Finset.range k).image (fun j => 2 ^ j), ∑ x ∈ S, x = m := by
  induction k with
  | zero =>
      intro m hm
      refine ⟨∅, by simp, ?_⟩
      simp only [Finset.sum_empty]
      simpa using (by omega : m = 0).symm
  | succ k ih =>
      intro m hm
      rcases lt_or_ge m (2 ^ k) with h | h
      · obtain ⟨S, hS, hSsum⟩ := ih m h
        exact ⟨S, hS.trans (image_range_subset k), hSsum⟩
      · have hm' : m - 2 ^ k < 2 ^ k := by
          have : (2:ℕ) ^ (k + 1) = 2 ^ k + 2 ^ k := by ring
          omega
        obtain ⟨S, hS, hSsum⟩ := ih _ hm'
        have hlt : ∀ x ∈ S, x < 2 ^ k := by
          intro x hx
          obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp (hS hx)
          exact Nat.pow_lt_pow_right (by norm_num) (Finset.mem_range.mp hj)
        have hnot : 2 ^ k ∉ S := fun hmem => absurd (hlt _ hmem) (lt_irrefl _)
        refine ⟨insert (2 ^ k) S, ?_, ?_⟩
        · refine Finset.insert_subset ?_ (hS.trans (image_range_subset k))
          exact Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (Nat.lt_succ_self k), rfl⟩
        · rw [Finset.sum_insert hnot, hSsum]
          omega

