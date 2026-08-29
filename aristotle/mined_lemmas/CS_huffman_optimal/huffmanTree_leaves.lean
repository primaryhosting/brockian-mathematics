import Mathlib

/-!
# Kraft's inequality for prefix-free codes
-/

namespace CS

open scoped BigOperators


theorem huffmanTree_leaves [Fintype α] [Nonempty α] (w : α → ℝ) :
    (huffmanTree w).leaves = (Finset.univ : Finset α).val := by
  have h := buildList_leaves w (leafList α).length (leafList α) rfl
  rw [buildList_leafList] at h
  have h1 : msLeaves (↑[huffmanTree w] : Multiset (HTree α)) = (huffmanTree w).leaves := by
    simp [msLeaves]
  have h2 : msLeaves (↑(leafList α) : Multiset (HTree α)) = (Finset.univ : Finset α).val := by
    rw [msLeaves, coe_leafList, Multiset.map_map]
    simpa using Multiset.sum_map_singleton (Finset.univ : Finset α).val
  rw [h1, h2] at h
  exact h

/-- The Huffman code of a finite weighted alphabet. -/
