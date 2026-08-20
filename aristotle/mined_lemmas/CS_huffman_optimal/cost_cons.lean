import RequestProject.HuffmanKraft

/-!
# Weighted depth multisets, the Huffman merging process, and the optimality bound
-/

namespace CS

/-- A *weighted depth multiset*: a finite multiset of pairs `(weight, codeword length)`. -/
abbrev WD := Multiset (ℝ × ℕ)

/-- The expected codeword length associated to a weighted depth multiset. -/

@[simp] theorem cost_cons (p : ℝ × ℕ) (D : WD) :
    cost (p ::ₘ D) = p.1 * (p.2 : ℝ) + cost D := by simp [cost]
