import RequestProject.HuffmanKraft

/-!
# Weighted depth multisets, the Huffman merging process, and the optimality bound
-/

namespace CS

/-- A *weighted depth multiset*: a finite multiset of pairs `(weight, codeword length)`. -/
abbrev WD := Multiset (ℝ × ℕ)

/-- The expected codeword length associated to a weighted depth multiset. -/

theorem card_allLists (n : ℕ) : (allLists n).card = 2 ^ n := by
  induction n with
  | zero => simp [allLists]
  | succ n ih =>
    rw [allLists, Finset.card_image_of_injective _ (by
      rintro ⟨b, l⟩ ⟨b', l'⟩ h
      simp only [List.cons.injEq] at h
      simp [h.1, h.2])]
    simp [ih, pow_succ, mul_comm]

/-- The finset of extensions of `u` to a word of length `M`. -/
