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

namespace Math

variable {α : Type*} [PartialOrder α] [Fintype α]

/-- The finset of all chains of a finite partial order. -/

lemma exists_longest_chain : ∃ C ∈ chainsFinset α, C.card = longestChain α := by
  obtain ⟨C, hC, hCcard⟩ :=
    Finset.exists_mem_eq_sup (chainsFinset α) chainsFinset_nonempty Finset.card
  exact ⟨C, hC, hCcard.symm⟩

