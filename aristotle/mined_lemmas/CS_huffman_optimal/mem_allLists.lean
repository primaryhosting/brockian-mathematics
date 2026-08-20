import RequestProject.HuffmanKraft

/-!
# Weighted depth multisets, the Huffman merging process, and the optimality bound
-/

namespace CS

/-- A *weighted depth multiset*: a finite multiset of pairs `(weight, codeword length)`. -/
abbrev WD := Multiset (ℝ × ℕ)

/-- The expected codeword length associated to a weighted depth multiset. -/

theorem mem_allLists {n : ℕ} {x : List Bool} : x ∈ allLists n ↔ x.length = n := by
  induction n generalizing x with
  | zero => simp [allLists, List.length_eq_zero_iff]
  | succ n ih =>
    simp only [allLists, Finset.mem_image, Finset.mem_product, Finset.mem_univ, true_and,
      Prod.exists]
    constructor
    · rintro ⟨b, l, hl, rfl⟩
      simp [ih.1 hl]
    · intro hx
      cases x with
      | nil => simp at hx
      | cons b l => exact ⟨b, l, ih.2 (by simpa using hx), rfl⟩

