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

open Finset

variable {α : Type*} [Fintype α] [PartialOrder α]

/-- The finset of all chains (as finsets) of a finite partial order. -/

lemma hgt_strictMono {x y : α} (hxy : x < y) : hgt x < hgt y := by
  obtain ⟨c, hc, hcard⟩ :=
    Finset.exists_mem_eq_sup ((chainFinsets α).filter (fun c => ∀ y ∈ c, y ≤ x))
      ⟨{x}, singleton_mem_hgtFinsets x⟩ Finset.card
  obtain ⟨hc1, hc2⟩ := Finset.mem_filter.1 hc
  have hchain : IsChain (· ≤ ·) (c : Set α) := mem_chainFinsets.1 hc1
  have hynotmem : y ∉ c := fun hy => absurd (hc2 y hy) (not_le_of_gt hxy)
  have hins : insert y c ∈ (chainFinsets α).filter (fun c => ∀ z ∈ c, z ≤ y) := by
    refine Finset.mem_filter.2 ⟨mem_chainFinsets.2 ?_, ?_⟩
    · have : ((insert y c : Finset α) : Set α) = insert y (c : Set α) := by
        simp
      rw [this]
      refine hchain.insert ?_
      intro b hb _
      exact Or.inr ((hc2 b (by simpa using hb)).trans hxy.le)
    · intro z hz
      rcases Finset.mem_insert.1 hz with h | h
      · exact h ▸ le_refl y
      · exact (hc2 z h).trans hxy.le
  have hle : (insert y c).card ≤ hgt y := Finset.le_sup (f := Finset.card) hins
  rw [Finset.card_insert_of_notMem hynotmem] at hle
  have hx : hgt x = c.card := hcard
  omega

