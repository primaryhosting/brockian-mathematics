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

lemma height_lt_height {x y : α} (hxy : x < y) : height x < height y := by
  classical
  obtain ⟨s, hsub, hchain, hcard⟩ :=
    exists_chain_card_eq (Finset.univ.filter (fun z => z ≤ x))
  have hy : y ∉ s := by
    intro hy
    have := hsub hy
    simp only [Finset.mem_filter] at this
    exact absurd (le_antisymm this.2 hxy.le) (by rintro rfl; exact absurd hxy (lt_irrefl _))
  have hsx : ∀ z ∈ s, z ≤ x := by
    intro z hz
    have := hsub hz
    simp only [Finset.mem_filter] at this
    exact this.2
  have hsub' : insert y s ⊆ Finset.univ.filter (fun z => z ≤ y) := by
    intro z hz
    rcases Finset.mem_insert.1 hz with rfl | hz
    · simp
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact le_trans (hsx z hz) hxy.le
  have hchain' : IsChain (· ≤ ·) ((insert y s : Finset α) : Set α) := by
    intro a ha b hb hab
    simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at ha hb
    rcases ha with rfl | ha
    · rcases hb with rfl | hb
      · exact absurd rfl hab
      · exact Or.inr (le_trans (hsx b hb) hxy.le)
    · rcases hb with rfl | hb
      · exact Or.inl (le_trans (hsx a ha) hxy.le)
      · exact hchain ha hb hab
  have hle := card_le_maxChainCardIn hsub' hchain'
  rw [Finset.card_insert_of_notMem hy] at hle
  have : height x + 1 ≤ height y := by
    simpa [height, hcard] using hle
  omega

/-- The fibers of the height function form an antichain cover of size at most
the length of a longest chain. -/
