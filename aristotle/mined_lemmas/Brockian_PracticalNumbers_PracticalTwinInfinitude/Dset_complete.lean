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

lemma Dset_complete (i : ℕ) : Complete (Dset i) := by
  induction i with
  | zero =>
      intro m hm
      have hsum : ∑ x ∈ (Dset 0), x = 3 := by decide
      rw [hsum] at hm
      interval_cases m
      · exact ⟨∅, by simp, by simp⟩
      · exact ⟨{1}, by decide, by decide⟩
      · exact ⟨{2}, by decide, by decide⟩
      · exact ⟨{1, 2}, by decide, by decide⟩
  | succ i ih =>
      show Complete (Dset i ∪ (Dset i).image (fun d => F i * d))
      refine complete_step (Dset i) (F i) (F_pos i) ih ?_ (Dset_disjoint i)
      have h1 := F_le_N_succ i
      have h2 := N_le_sum_Dset i
      omega

