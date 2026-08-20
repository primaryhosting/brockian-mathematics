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

lemma height_lt_height_of_lt {a b : α} (hab : a < b) : height a < height b := by
  obtain ⟨s, hchain, hle, hcard⟩ := exists_height_chain a
  have hb : b ∉ s := fun hb => absurd (lt_of_lt_of_le hab (hle b hb)) (lt_irrefl a)
  have hchain' : IsChain (· ≤ ·) ((insert b s : Finset α) : Set α) := by
    rw [Finset.coe_insert]
    refine hchain.insert ?_
    intro x hx _
    exact Or.inr (le_of_lt (lt_of_le_of_lt (hle x (by simpa using hx)) hab))
  have hmem : (insert b s : Finset α) ∈ (chains α).filter fun t => ∀ x ∈ t, x ≤ b := by
    refine Finset.mem_filter.mpr ⟨mem_chains.mpr hchain', ?_⟩
    intro x hx
    rcases Finset.mem_insert.mp hx with h | h
    · exact h ▸ le_refl b
    · exact le_of_lt (lt_of_le_of_lt (hle x h) hab)
  have := Finset.le_sup (f := Finset.card) hmem
  rw [Finset.card_insert_of_notMem hb, hcard] at this
  have hb2 : height a + 1 ≤ height b := this
  omega

/-- **Mirsky's theorem** (the dual form of Dilworth's theorem): in a finite partial order,
the minimum number of antichains needed to cover the poset equals the size of a longest
chain. -/
