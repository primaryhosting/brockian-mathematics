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

lemma exists_antichain_cover :
    ∃ F : Finset (Finset α), IsAntichainCover F ∧ F.card ≤ longestChain α := by
  classical
  refine ⟨(Finset.Icc 1 (longestChain α)).image
      (fun n => Finset.univ.filter (fun x : α => height x = n)), ⟨?_, ?_⟩, ?_⟩
  · intro s hs
    simp only [Finset.mem_image, Finset.mem_Icc] at hs
    obtain ⟨n, _, rfl⟩ := hs
    intro a ha b hb hab hle
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at ha hb
    have : height a < height b := height_lt_height (lt_of_le_of_ne hle hab)
    omega
  · intro x
    refine ⟨Finset.univ.filter (fun z : α => height z = height x), ?_, by simp⟩
    simp only [Finset.mem_image, Finset.mem_Icc]
    exact ⟨height x, ⟨one_le_height x, height_le_longestChain x⟩, rfl⟩
  · calc ((Finset.Icc 1 (longestChain α)).image
        (fun n => Finset.univ.filter (fun x : α => height x = n))).card
        ≤ (Finset.Icc 1 (longestChain α)).card := Finset.card_image_le
      _ = longestChain α := by simp

/-- A chain meets every antichain in at most one element, hence any antichain cover
has at least as many parts as the length of a longest chain. -/
