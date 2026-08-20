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

/-!
## Practical numbers and practical twins

A positive integer `n` is *practical* if every `m ≤ σ(n)` is a sum of distinct divisors of `n`.
The *practical twin* problem asks whether there are infinitely many `n` such that both `n` and
`n + 2` are practical (this is a known but genuinely deep statement, proved by sieve methods;
no unconditional proof is formalised here).

This file develops:

* `IsPractical`, `DivisorComplete` and the equivalence `isPractical_iff_divisorComplete`
  between practicality and the elementary divisor-chain criterion "every divisor is at most one
  more than the sum of the smaller divisors";
* decidability of the criterion, and explicit practical twin pairs up to `(8190, 8192)`;
* `isPractical_two_pow`, `infinite_practical`: powers of two are practical, so there are
  infinitely many practical numbers;
* `isPractical_mul_prime`: the coprime case of Stewart's multiplication theorem, and the family
  `isPractical_prime_mul_two_pow`;
* `practicalTwinConjecture_iff` and `PracticalTwinInfinitude`: a Lean-checked reduction of the
  practical twin conjecture to the elementary criterion.
-/

set_option maxRecDepth 10000

open Finset

namespace Brockian.PracticalNumbers

/-- A positive integer `n` is *practical* if every `m ≤ σ(n)` is the sum of a set of
pairwise distinct divisors of `n`. -/

theorem subsetSum_of_complete (S : Finset ℕ)
    (h : ∀ a ∈ S, a ≤ 1 + ∑ b ∈ S.filter (· < a), b) :
    ∀ m ≤ ∑ b ∈ S, b, ∃ T ⊆ S, ∑ b ∈ T, b = m := by
  induction S using Finset.strongInduction with
  | _ S ih =>
    intro m hm
    rcases S.eq_empty_or_nonempty with rfl | hne
    · refine ⟨∅, by simp, ?_⟩
      simp only [Finset.sum_empty] at hm
      simp [Nat.le_zero.1 hm]
    · set a := S.max' hne with ha_def
      have ha : a ∈ S := S.max'_mem hne
      have hfil : S.filter (· < a) = S.erase a := by
        ext x
        simp only [mem_filter, mem_erase]
        constructor
        · rintro ⟨hx, hlt⟩; exact ⟨by omega, hx⟩
        · rintro ⟨hne', hx⟩
          exact ⟨hx, lt_of_le_of_ne (S.le_max' x hx) hne'⟩
      have hss : S.erase a ⊂ S := erase_ssubset ha
      have hih : ∀ b ∈ S.erase a, b ≤ 1 + ∑ c ∈ (S.erase a).filter (· < b), c := by
        intro b hb
        have hb' : b ∈ S := mem_of_mem_erase hb
        have hfb : (S.erase a).filter (· < b) = S.filter (· < b) := by
          ext x
          simp only [mem_filter, mem_erase]
          constructor
          · rintro ⟨⟨_, hx⟩, hlt⟩; exact ⟨hx, hlt⟩
          · rintro ⟨hx, hlt⟩
            refine ⟨⟨?_, hx⟩, hlt⟩
            rintro rfl
            exact absurd (S.le_max' b hb') (by omega)
        rw [hfb]; exact h b hb'
      have hsum : ∑ b ∈ S, b = a + ∑ b ∈ S.erase a, b := (Finset.add_sum_erase S _ ha).symm
      by_cases hcase : m ≤ ∑ b ∈ S.erase a, b
      · obtain ⟨T, hT, hTsum⟩ := ih _ hss hih m hcase
        exact ⟨T, hT.trans (erase_subset _ _), hTsum⟩
      · push_neg at hcase
        have hale : a ≤ m := by
          have := h a ha
          rw [hfil] at this
          omega
        have hle : m - a ≤ ∑ b ∈ S.erase a, b := by omega
        obtain ⟨T, hT, hTsum⟩ := ih _ hss hih (m - a) hle
        have haT : a ∉ T := fun hc => (Finset.notMem_erase a S) (hT hc)
        refine ⟨insert a T, ?_, ?_⟩
        · intro x hx
          rcases mem_insert.1 hx with rfl | hx
          · exact ha
          · exact (hT.trans (erase_subset _ _)) hx
        · rw [Finset.sum_insert haT, hTsum]; omega

/-- The divisor-chain criterion characterises practical numbers. -/
