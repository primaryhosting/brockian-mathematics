/-
# Dilworth
Category: Pure Mathematics
Target: Math.dilworth
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Math

variable {α : Type*} [Fintype α] [PartialOrder α]

/-- A colouring of the poset by `{0, …, n-1}` whose colour classes are antichains. -/

lemma exists_chain_card_eq : ∃ C : Finset α, IsChain (· ≤ ·) (C : Set α) ∧
    C.card = longestChain α := by
  have hne : (chains α).Nonempty := ⟨∅, by simp [mem_chains]⟩
  obtain ⟨C, hC, hcard⟩ := Finset.exists_mem_eq_sup (chains α) hne Finset.card
  exact ⟨C, mem_chains.mp hC, hcard.symm⟩

