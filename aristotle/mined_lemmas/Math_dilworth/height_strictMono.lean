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

lemma height_strictMono {x y : α} (hxy : x < y) : height x < height y := by
  have hne : ((chainsFinset α).filter (fun C => ∀ z ∈ C, z ≤ x)).Nonempty := by
    refine ⟨{x}, ?_⟩
    simp only [Finset.mem_filter, mem_chainsFinset]
    refine ⟨by simp, ?_⟩
    intro z hz
    simp only [Finset.mem_singleton] at hz
    exact hz.le
  obtain ⟨C, hC, hCcard⟩ := Finset.exists_mem_eq_sup _ hne Finset.card
  simp only [Finset.mem_filter, mem_chainsFinset] at hC
  obtain ⟨hchain, hle⟩ := hC
  have hyC : y ∉ C := by
    intro hy
    exact absurd (lt_of_lt_of_le hxy (hle y hy)) (lt_irrefl x)
  have hins : (insert y C) ∈ (chainsFinset α).filter (fun C => ∀ z ∈ C, z ≤ y) := by
    simp only [Finset.mem_filter, mem_chainsFinset]
    constructor
    · rw [Finset.coe_insert]
      refine hchain.insert ?_
      intro b hb _
      exact Or.inr (le_trans (hle b (by exact_mod_cast hb)) hxy.le)
    · intro z hz
      rcases Finset.mem_insert.1 hz with h | h
      · exact h.le
      · exact le_trans (hle z h) hxy.le
  have h1 : (insert y C).card = C.card + 1 := Finset.card_insert_of_notMem hyC
  have h2 : (insert y C).card ≤ height y := Finset.le_sup (f := Finset.card) hins
  rw [height, hCcard]
  omega

