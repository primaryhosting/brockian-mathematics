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

lemma exists_chain_height' (x : α) : ∃ C : Finset α, IsChain (· ≤ ·) (C : Set α) ∧ x ∈ C ∧
    (∀ z ∈ C, z ≤ x) ∧ C.card = height' x := by
  have hne : ((chains α).filter (fun C => x ∈ C ∧ ∀ z ∈ C, z ≤ x)).Nonempty := by
    refine ⟨{x}, ?_⟩
    simp [chains, IsChain, Set.Pairwise]
  obtain ⟨C, hC, hcard⟩ := Finset.exists_mem_eq_sup _ hne Finset.card
  rw [Finset.mem_filter] at hC
  exact ⟨C, mem_chains.mp hC.1, hC.2.1, hC.2.2, hcard.symm⟩

