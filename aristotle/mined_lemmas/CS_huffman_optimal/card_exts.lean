import RequestProject.HuffmanKraft

/-!
# Weighted depth multisets, the Huffman merging process, and the optimality bound
-/

namespace CS

/-- A *weighted depth multiset*: a finite multiset of pairs `(weight, codeword length)`. -/
abbrev WD := Multiset (ℝ × ℕ)

/-- The expected codeword length associated to a weighted depth multiset. -/

theorem card_exts {M : ℕ} {u : List Bool} (h : u.length ≤ M) :
    (exts M u).card = 2 ^ (M - u.length) := by
  have himg : exts M u = (allLists (M - u.length)).image (fun y => u ++ y) := by
    ext x
    simp only [exts, Finset.mem_filter, mem_allLists, Finset.mem_image]
    constructor
    · rintro ⟨hx, hpre⟩
      obtain ⟨t, rfl⟩ := hpre
      refine ⟨t, ?_, rfl⟩
      simp only [List.length_append] at hx
      omega
    · rintro ⟨y, hy, rfl⟩
      refine ⟨?_, ⟨y, rfl⟩⟩
      simp only [List.length_append]
      omega
  rw [himg, Finset.card_image_of_injective _ (fun a b hab => List.append_cancel_left hab),
    card_allLists]

/-- Kraft's inequality: for a prefix-free list of binary codewords,
`∑ (1/2)^(length u) ≤ 1`. -/
