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
-- (Lean requires `import` to precede any doc-comment command, so the header above is written as a
-- plain block comment; its text is verbatim as requested.)

import Mathlib

/-!
The main result of this file is `Brockian.PracticalNumbers.PracticalTwinInfinitude`:
there are infinitely many `n` such that both `n` and `n + 2` are practical numbers.

The proof is completely explicit. We show that for every `t`, the pair
`(2 * (3 ^ 2 ^ t - 1), 2 * 3 ^ 2 ^ t)` is a pair of practical numbers differing by `2`
(e.g. `(4, 6)`, `(16, 18)`, `(160, 162)`, `(13120, 13122)`, ...).

The engine is the classical closure property `IsPractical.mul`: if `n` is practical and
`0 < m ≤ σ n + 1`, then `n * m` is practical. Iterating it along the factorisation
`3 ^ 2 ^ t - 1 = 2 * (3 ^ 2 ^ 0 + 1) * (3 ^ 2 ^ 1 + 1) * ⋯ * (3 ^ 2 ^ (t-1) + 1)`
(realised here as a simple induction on `t`) yields practicality of `2 * (3 ^ 2 ^ t - 1)`,
while practicality of `2 * 3 ^ a` is an even simpler induction.
-/

namespace Brockian.PracticalNumbers

open Finset

/-- `n` is a *practical number* if it is positive and every `k ≤ n` can be written as a sum of
distinct divisors of `n`. -/

theorem exists_subset_sum_of_chain {S : Finset ℕ} (hpos : ∀ x ∈ S, 0 < x)
    (h : ∀ x ∈ S, x ≤ 1 + ∑ y ∈ S.filter (· < x), y) :
    ∀ k ≤ ∑ x ∈ S, x, ∃ T ⊆ S, ∑ x ∈ T, x = k := by
  induction S using Finset.strongInduction with
  | _ S ih =>
    intro k hk
    rcases S.eq_empty_or_nonempty with rfl | hne
    · simp only [Finset.sum_empty, Nat.le_zero] at hk
      exact ⟨∅, by simp [hk]⟩
    · set M := S.max' hne with hMdef
      have hM : M ∈ S := S.max'_mem hne
      set S' := S.erase M with hS'def
      have hsub : S' ⊂ S := Finset.erase_ssubset hM
      have hfil : ∀ x ∈ S', S'.filter (· < x) = S.filter (· < x) := by
        intro x hx
        have hxS : x ∈ S := Finset.mem_of_mem_erase hx
        apply Finset.Subset.antisymm
        · exact Finset.filter_subset_filter _ (Finset.erase_subset _ _)
        · intro y hy
          simp only [Finset.mem_filter] at hy ⊢
          refine ⟨Finset.mem_erase.2 ⟨?_, hy.1⟩, hy.2⟩
          intro hyM
          have : x ≤ M := S.le_max' x hxS
          omega
      have hpos' : ∀ x ∈ S', 0 < x := fun x hx => hpos x (Finset.mem_of_mem_erase hx)
      have h' : ∀ x ∈ S', x ≤ 1 + ∑ y ∈ S'.filter (· < x), y := by
        intro x hx
        rw [hfil x hx]
        exact h x (Finset.mem_of_mem_erase hx)
      have hsum : ∑ x ∈ S', x + M = ∑ x ∈ S, x := Finset.sum_erase_add _ _ hM
      by_cases hk' : k ≤ ∑ x ∈ S', x
      · obtain ⟨T, hT, hTsum⟩ := ih S' hsub hpos' h' k hk'
        exact ⟨T, hT.trans (Finset.erase_subset _ _), hTsum⟩
      · push_neg at hk'
        have hMle : M ≤ 1 + ∑ x ∈ S', x := by
          refine le_trans (h M hM) ?_
          have hsubf : S.filter (· < M) ⊆ S' := by
            intro y hy
            simp only [Finset.mem_filter] at hy
            exact Finset.mem_erase.2 ⟨by omega, hy.1⟩
          exact Nat.add_le_add_left (Finset.sum_le_sum_of_subset hsubf) 1
        have hMk : M ≤ k := by omega
        obtain ⟨T, hT, hTsum⟩ := ih S' hsub hpos' h' (k - M) (by omega)
        refine ⟨insert M T, ?_, ?_⟩
        · intro x hx
          rcases Finset.mem_insert.1 hx with rfl | hx
          · exact hM
          · exact (hT.trans (Finset.erase_subset _ _)) hx
        · have hMT : M ∉ T := fun hc => (Finset.mem_erase.1 (hT hc)).1 rfl
          rw [Finset.sum_insert hMT, hTsum]
          omega

/-- For a practical number, each divisor is at most one more than the sum of the smaller
divisors. -/
