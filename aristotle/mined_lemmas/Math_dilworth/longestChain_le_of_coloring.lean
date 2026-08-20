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

lemma longestChain_le_of_coloring {n : ℕ} {f : α → ℕ} (hf : IsAntichainColoring n f) :
    longestChain α ≤ n := by
  obtain ⟨C, hC, hcard⟩ := exists_chain_card_eq (α := α)
  have hinj : Set.InjOn f (C : Set α) := by
    intro a ha b hb hab
    by_cases h : a = b
    · exact h
    · rcases hC ha hb h with h1 | h1
      · exact hf.2 a b hab h1
      · exact (hf.2 b a hab.symm h1).symm
  have hmap : Set.MapsTo f (C : Set α) ((Finset.range n : Finset ℕ) : Set ℕ) := by
    intro a _
    simpa using hf.1 a
  have := Finset.card_le_card_of_injOn f hmap hinj
  simpa [hcard] using this

/-- **Mirsky's theorem** (the dual of Dilworth's theorem): in a finite poset, the minimum
number of antichains needed to cover the poset equals the number of elements of a longest
chain. -/
