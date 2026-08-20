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

lemma exists_small_cover :
    ∃ S : Finset (Finset α), IsAntichainCover S ∧ S.card ≤ longestChain α := by
  set S : Finset (Finset α) :=
    (Finset.Icc 1 (longestChain α)).image
      (fun k => Finset.univ.filter (fun x : α => height x = k)) with hS
  have hcover : IsAntichainCover S := by
    constructor
    · intro A hA
      simp only [hS, Finset.mem_image] at hA
      obtain ⟨k, _, rfl⟩ := hA
      exact isAntichain_level k
    · intro x
      refine ⟨Finset.univ.filter (fun z : α => height z = height x), ?_, by simp⟩
      simp only [hS, Finset.mem_image]
      exact ⟨height x, Finset.mem_Icc.2 ⟨one_le_height x, height_le_longestChain x⟩, rfl⟩
  have hcard : S.card ≤ longestChain α := by
    calc S.card ≤ (Finset.Icc 1 (longestChain α)).card := Finset.card_image_le
      _ = longestChain α := by simp
  exact ⟨S, hcover, hcard⟩

