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

theorem dilworth (α : Type*) [Fintype α] [PartialOrder α] :
    minAntichainCover α = longestChain α := by
  have hmem : longestChain α ∈ {n : ℕ | ∃ f : α → ℕ, IsAntichainColoring n f} :=
    coverable_longestChain
  refine le_antisymm (Nat.sInf_le hmem) ?_
  have hne : {n : ℕ | ∃ f : α → ℕ, IsAntichainColoring n f}.Nonempty := ⟨_, hmem⟩
  obtain ⟨f, hf⟩ := Nat.sInf_mem hne
  exact longestChain_le_of_coloring hf

/-- Sanity check: the two-element chain `Fin 2` has longest chain of size `2`, hence needs
two antichains to be covered. -/
example : minAntichainCover (Fin 2) = 2 := by
  rw [dilworth]
  refine le_antisymm (Finset.sup_le ?_) ?_
  · intro C _
    simpa using Finset.card_le_univ C
  · have hchain : IsChain (· ≤ ·) ((Finset.univ : Finset (Fin 2)) : Set (Fin 2)) := by
      intro a _ b _ _
      rcases le_total a b with h | h
      · exact Or.inl h
      · exact Or.inr h
    simpa using card_le_longestChain hchain

end Math

