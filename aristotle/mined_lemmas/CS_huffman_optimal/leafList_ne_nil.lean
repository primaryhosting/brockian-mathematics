import Mathlib

/-!
# Kraft's inequality for prefix-free codes
-/

namespace CS

open scoped BigOperators


theorem leafList_ne_nil [Fintype α] [Nonempty α] : leafList α ≠ [] := by
  intro h
  have : ((leafList α : List (HTree α)) : Multiset (HTree α)) = 0 := by rw [h]; rfl
  rw [coe_leafList] at this
  have hcard : (Finset.univ : Finset α).card = 0 := by
    simpa using congrArg Multiset.card this
  simp [Finset.card_univ] at hcard
  exact absurd hcard (Fintype.card_ne_zero)

/-- The Huffman tree of a finite weighted alphabet. -/
