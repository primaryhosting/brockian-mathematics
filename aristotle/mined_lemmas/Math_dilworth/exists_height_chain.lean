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

variable {α : Type*} [Fintype α] [PartialOrder α]

/-- The finset of all chains (as finsets) of a finite partial order. -/

lemma exists_height_chain (a : α) :
    ∃ s : Finset α, IsChain (· ≤ ·) (s : Set α) ∧ (∀ x ∈ s, x ≤ a) ∧ s.card = height a := by
  have hne : ((chains α).filter fun s => ∀ x ∈ s, x ≤ a).Nonempty :=
    ⟨{a}, by simp [mem_chains, IsChain, Set.Pairwise]⟩
  obtain ⟨s, hs, hcard⟩ := Finset.exists_mem_eq_sup _ hne Finset.card
  rw [Finset.mem_filter, mem_chains] at hs
  exact ⟨s, hs.1, hs.2, hcard.symm⟩

