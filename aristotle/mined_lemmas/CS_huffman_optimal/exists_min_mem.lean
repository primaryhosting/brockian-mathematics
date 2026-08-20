import RequestProject.HuffmanKraft

/-!
# Weighted depth multisets, the Huffman merging process, and the optimality bound
-/

namespace CS

/-- A *weighted depth multiset*: a finite multiset of pairs `(weight, codeword length)`. -/
abbrev WD := Multiset (ℝ × ℕ)

/-- The expected codeword length associated to a weighted depth multiset. -/

theorem exists_min_mem {α : Type*} [LinearOrder α] (s : Multiset α) (hs : s ≠ 0) :
    ∃ m ∈ s, ∀ x ∈ s, m ≤ x := by
  induction s using Multiset.induction with
  | empty => exact absurd rfl hs
  | cons a s ih =>
    rcases eq_or_ne s 0 with rfl | hne
    · exact ⟨a, by simp, by simp⟩
    · obtain ⟨m, hm, hmin⟩ := ih hne
      rcases le_total a m with hle | hle
      · refine ⟨a, Multiset.mem_cons_self _ _, ?_⟩
        intro x hx
        rcases Multiset.mem_cons.1 hx with rfl | hx
        · exact le_refl _
        · exact le_trans hle (hmin x hx)
      · refine ⟨m, Multiset.mem_cons_of_mem hm, ?_⟩
        intro x hx
        rcases Multiset.mem_cons.1 hx with rfl | hx
        · exact hle
        · exact hmin x hx

/-- The Kraft sum scaled by `2 ^ M`, as a natural number. -/
