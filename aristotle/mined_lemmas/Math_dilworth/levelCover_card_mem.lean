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

lemma levelCover_card_mem : (levelCover α).card ∈ antichainCoverCards α := by
  refine ⟨levelCover α, rfl, ?_, ?_⟩
  · intro A hA
    rw [levelCover, Finset.mem_image] at hA
    obtain ⟨i, _, rfl⟩ := hA
    exact isAntichain_rk_level i
  · intro x
    refine ⟨Finset.univ.filter (fun z : α => rk z = rk x), ?_, ?_⟩
    · rw [levelCover, Finset.mem_image]
      exact ⟨rk x, Finset.mem_Icc.2 ⟨rk_pos x, rk_le_longestChain x⟩, rfl⟩
    · simp

