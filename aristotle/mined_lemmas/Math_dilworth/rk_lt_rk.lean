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

variable {α : Type*} [Fintype α] [PartialOrder α]

/-- The finset of all chains (as finsets) of a finite partial order. -/

lemma rk_lt_rk {x y : α} (h : x < y) : rk x < rk y := by
  obtain ⟨C, hC, hCsup⟩ :=
    Finset.exists_mem_eq_sup (chainsBelow x) ⟨∅, by rw [mem_chainsBelow]; simp⟩ Finset.card
  rw [mem_chainsBelow] at hC
  obtain ⟨hchain, hbelow⟩ := hC
  have hy : y ∉ C := by
    intro hyC
    exact absurd (hbelow y hyC) h.not_ge
  have hins : insert y C ∈ chainsBelow y := by
    rw [mem_chainsBelow]
    constructor
    · have : IsChain (· ≤ ·) (insert y (C : Set α)) := by
        refine hchain.insert ?_
        intro b hb _
        exact Or.inr (le_trans (hbelow b (by simpa using hb)) h.le)
      simpa using this
    · intro z hz
      rcases Finset.mem_insert.1 hz with rfl | hz
      · exact le_refl _
      · exact le_trans (hbelow z hz) h.le
  have hcard : (insert y C).card = C.card + 1 := Finset.card_insert_of_notMem hy
  have := Finset.le_sup (f := Finset.card) hins
  rw [hcard] at this
  simp only [rk]
  omega

