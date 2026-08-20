/-
# Dilworth
Category: Pure Mathematics
Target: Math.dilworth
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Dilworth
Category: Pure Mathematics
Target: Math.dilworth
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Math

open Finset

variable {α : Type*} [Fintype α] [PartialOrder α]

open Classical in
/-- `chainHeight x` is the largest cardinality of a chain all of whose elements are `≤ x`. -/

lemma isGreatest_maxChainCard (α : Type*) [Fintype α] [PartialOrder α] :
    IsGreatest {n : ℕ | ∃ s : Finset α, IsChain (· ≤ ·) (s : Set α) ∧ s.card = n}
      (maxChainCard α) := by
  classical
  constructor
  · obtain ⟨s, -, hs⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Finset α))
      ⟨(∅ : Finset α), Finset.mem_univ _⟩
      (fun s : Finset α => if IsChain (· ≤ ·) (s : Set α) then s.card else 0)
    by_cases hc : IsChain (· ≤ ·) (s : Set α)
    · exact ⟨s, hc, by rw [maxChainCard, hs, if_pos hc]⟩
    · refine ⟨(∅ : Finset α), Set.Subsingleton.isChain (by simp), ?_⟩
      rw [maxChainCard, hs, if_neg hc]
      simp
  · rintro n ⟨s, hs, rfl⟩
    have hsup := Finset.le_sup (f := fun s : Finset α =>
        if IsChain (· ≤ ·) (s : Set α) then s.card else 0) (Finset.mem_univ s)
    simp only [] at hsup
    rw [if_pos hs] at hsup
    exact hsup

/-- **Mirsky's theorem** (the dual of Dilworth's theorem): in a finite partial order, the
minimum number of antichains needed to cover the whole order equals the maximum size of a
chain. -/
