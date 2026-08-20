import RequestProject.HuffmanKraft

/-!
# Weighted depth multisets, the Huffman merging process, and the optimality bound
-/

namespace CS

/-- A *weighted depth multiset*: a finite multiset of pairs `(weight, codeword length)`. -/
abbrev WD := Multiset (ℝ × ℕ)

/-- The expected codeword length associated to a weighted depth multiset. -/

@[simp] theorem kn_cons (M : ℕ) (p : ℝ × ℕ) (D : WD) :
    kn M (p ::ₘ D) = 2 ^ (M - p.2) + kn M D := by simp [kn]

