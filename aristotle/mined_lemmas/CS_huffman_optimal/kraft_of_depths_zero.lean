import RequestProject.HuffmanKraft

/-!
# Weighted depth multisets, the Huffman merging process, and the optimality bound
-/

namespace CS

/-- A *weighted depth multiset*: a finite multiset of pairs `(weight, codeword length)`. -/
abbrev WD := Multiset (ℝ × ℕ)

/-- The expected codeword length associated to a weighted depth multiset. -/

theorem kraft_of_depths_zero {D : WD} (h : ∀ p ∈ D, p.2 = 0) : kraft D = D.card := by
  induction D using Multiset.induction with
  | empty => simp
  | cons a D ih =>
    rw [kraft_cons, h a (Multiset.mem_cons_self _ _),
      ih fun p hp => h p (Multiset.mem_cons_of_mem hp)]
    simp
    ring

/-- If the Kraft sum equals `1` and the maximal length `M` is positive, then at least two
codewords have length `M`. -/
