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
# Practical Twin Infinitude
Category: Brockian Conjecture
Target: Brockian.PracticalNumbers.PracticalTwinInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Finset

namespace Brockian.PracticalNumbers

/-- A positive natural number `n` is *practical* when every `m ≤ n` can be written as a sum
of distinct divisors of `n`. -/

lemma exists_subset_sum_of_chain :
    ∀ D : Finset ℕ, (∀ x ∈ D, x ≤ 1 + ∑ y ∈ D.filter (fun y => y < x), y) →
      ∀ m ≤ ∑ x ∈ D, x, ∃ S ⊆ D, ∑ d ∈ S, d = m := by
  intro D
  induction D using Finset.strongInduction with
  | _ D IH =>
    intro hchain m hm
    rcases D.eq_empty_or_nonempty with rfl | hne
    · simp only [Finset.sum_empty, Nat.le_zero] at hm
      exact ⟨∅, by simp [hm]⟩
    · set x0 := D.max' hne with hx0def
      have hx0D : x0 ∈ D := D.max'_mem hne
      set D' := D.erase x0 with hD'def
      have hsub : D' ⊂ D := Finset.erase_ssubset hx0D
      have hfilter : D.filter (fun y => y < x0) = D' := by
        ext y
        simp only [Finset.mem_filter, hD'def, Finset.mem_erase]
        constructor
        · rintro ⟨hy, hlt⟩; exact ⟨ne_of_lt hlt, hy⟩
        · rintro ⟨hne', hy⟩
          exact ⟨hy, lt_of_le_of_ne (D.le_max' y hy) hne'⟩
      have hsum : ∑ x ∈ D, x = x0 + ∑ x ∈ D', x := (Finset.add_sum_erase _ _ hx0D).symm
      have hchain' : ∀ x ∈ D', x ≤ 1 + ∑ y ∈ D'.filter (fun y => y < x), y := by
        intro x hx
        have hxD : x ∈ D := Finset.mem_of_mem_erase hx
        have heq : D'.filter (fun y => y < x) = D.filter (fun y => y < x) := by
          ext y
          simp only [Finset.mem_filter, hD'def, Finset.mem_erase]
          constructor
          · rintro ⟨⟨_, hy⟩, hlt⟩; exact ⟨hy, hlt⟩
          · rintro ⟨hy, hlt⟩
            refine ⟨⟨?_, hy⟩, hlt⟩
            rintro rfl
            exact absurd (D.le_max' x hxD) (not_le.mpr hlt)
        rw [heq]
        exact hchain x hxD
      by_cases hcase : m ≤ ∑ x ∈ D', x
      · obtain ⟨S, hS, hSsum⟩ := IH D' hsub hchain' m hcase
        exact ⟨S, hS.trans (Finset.erase_subset _ _), hSsum⟩
      · push_neg at hcase
        have hx0le : x0 ≤ m := by
          have := hchain x0 hx0D
          rw [hfilter] at this
          omega
        have hle : m - x0 ≤ ∑ x ∈ D', x := by omega
        obtain ⟨S, hS, hSsum⟩ := IH D' hsub hchain' (m - x0) hle
        have hx0S : x0 ∉ S := fun h => (Finset.mem_erase.mp (hS h)).1 rfl
        refine ⟨insert x0 S, ?_, ?_⟩
        · exact Finset.insert_subset hx0D (hS.trans (Finset.erase_subset _ _))
        · rw [Finset.sum_insert hx0S, hSsum]
          omega

/-- For a practical number, each divisor is at most one more than the sum of the smaller
divisors. -/
