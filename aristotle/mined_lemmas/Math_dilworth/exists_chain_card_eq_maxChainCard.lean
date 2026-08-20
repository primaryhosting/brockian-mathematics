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

section Mirsky

variable {α : Type*} [Fintype α] [PartialOrder α]

/-- The finset of all chains of a finite partial order. -/

lemma exists_chain_card_eq_maxChainCard :
    ∃ C : Finset α, IsChain (· ≤ ·) (↑C : Set α) ∧ C.card = maxChainCard α := by
  obtain ⟨C, hC, hcard⟩ :=
    Finset.exists_mem_eq_sup (chainsOf α) chainsOf_nonempty Finset.card
  exact ⟨C, mem_chainsOf.1 hC, hcard.symm⟩

