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

set_option grind.warning false

namespace Math

variable {α : Type*} [PartialOrder α]

/-- The finset of all chains (as finsets) contained in a given finset `t`. -/

lemma exists_chain_card_eq (t : Finset α) :
    ∃ s : Finset α, s ⊆ t ∧ IsChain (· ≤ ·) (s : Set α) ∧ s.card = maxChainCardIn t := by
  have hne : (chainsIn t).Nonempty := ⟨∅, mem_chainsIn.2 ⟨Finset.empty_subset _, by simp⟩⟩
  obtain ⟨s, hs, hsup⟩ := Finset.exists_mem_eq_sup (chainsIn t) hne Finset.card
  obtain ⟨h1, h2⟩ := mem_chainsIn.1 hs
  exact ⟨s, h1, h2, (hsup).symm⟩

variable [Fintype α]

/-- The length of a longest chain in the (finite) poset `α`. -/
