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

lemma one_le_height (x : α) : 1 ≤ height x := by
  have hx : ({x} : Finset α) ∈ (chainsFinset α).filter (fun C => ∀ y ∈ C, y ≤ x) := by
    simp only [Finset.mem_filter, mem_chainsFinset]
    refine ⟨?_, ?_⟩
    · simp
    · intro y hy
      simp only [Finset.mem_singleton] at hy
      exact hy.le
  have h := Finset.le_sup (f := Finset.card) hx
  simp only [Finset.card_singleton] at h
  exact h

