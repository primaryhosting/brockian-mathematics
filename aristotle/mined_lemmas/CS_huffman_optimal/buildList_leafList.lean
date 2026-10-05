import Mathlib

/-!
# Kraft's inequality for prefix-free codes
-/

namespace CS

open scoped BigOperators


theorem buildList_leafList [Fintype α] [Nonempty α] (w : α → ℝ) :
    buildList w (leafList α) = [huffmanTree w] := by
  obtain ⟨t, ht⟩ := exists_buildList_singleton w (leafList α) leafList_ne_nil
  rw [huffmanTree, ht]
  rfl

