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

lemma height'_strictMono {x y : α} (hxy : x < y) : height' x < height' y := by
  obtain ⟨C, hC, hxC, hle, hcard⟩ := exists_chain_height' x
  have hyC : y ∉ C := by
    intro hy
    exact absurd (lt_of_lt_of_le hxy (hle y hy)) (lt_irrefl x)
  have hchain : IsChain (· ≤ ·) ((insert y C : Finset α) : Set α) := by
    intro a ha b hb hab
    simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at ha hb
    rcases ha with rfl | ha
    · rcases hb with rfl | hb
      · exact absurd rfl hab
      · exact Or.inr (le_trans (hle b hb) hxy.le)
    · rcases hb with rfl | hb
      · exact Or.inl (le_trans (hle a ha) hxy.le)
      · exact hC ha hb hab
  have hmem : (insert y C : Finset α) ∈
      (chains α).filter (fun C => y ∈ C ∧ ∀ z ∈ C, z ≤ y) := by
    refine Finset.mem_filter.mpr ⟨mem_chains.mpr hchain, Finset.mem_insert_self _ _, ?_⟩
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact le_rfl
    · exact le_trans (hle z hz) hxy.le
  have hle2 : (insert y C).card ≤ height' y := Finset.le_sup (f := Finset.card) hmem
  rw [Finset.card_insert_of_notMem hyC, hcard] at hle2
  omega

