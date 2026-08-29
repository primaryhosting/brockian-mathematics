import Mathlib

/-!
# Dilworth
Category: Pure Mathematics
Target: Math.dilworth
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Classical

namespace Math

variable {α : Type*} [Fintype α] [PartialOrder α]

/-- The largest cardinality of a chain contained in the finite set `t`. -/

lemma exists_cover_card_le_longestChainCard :
    ∃ F : Finset (Finset α), F.card ≤ longestChainCard α ∧ IsAntichainCover F := by
  refine ⟨(Finset.Icc 1 (longestChainCard α)).image
      (fun i => Finset.univ.filter fun x : α => height x = i), ?_, ?_, ?_⟩
  · exact le_trans (Finset.card_image_le) (by simp)
  · intro s hs
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hs
    exact antichain_level i
  · intro x
    refine ⟨Finset.univ.filter fun y : α => height y = height x, ?_, by simp⟩
    exact Finset.mem_image.mpr
      ⟨height x, Finset.mem_Icc.mpr ⟨one_le_height x, height_le_longestChainCard x⟩, rfl⟩

/-- **Mirsky's theorem** (the dual of Dilworth's theorem): in a finite poset, the minimum
number of antichains needed to cover the poset equals the length of a longest chain. -/
