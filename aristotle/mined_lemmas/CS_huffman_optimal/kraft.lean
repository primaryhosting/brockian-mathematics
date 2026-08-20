import RequestProject.HuffmanKraft

/-!
# Weighted depth multisets, the Huffman merging process, and the optimality bound
-/

namespace CS

/-- A *weighted depth multiset*: a finite multiset of pairs `(weight, codeword length)`. -/
abbrev WD := Multiset (ℝ × ℕ)

/-- The expected codeword length associated to a weighted depth multiset. -/

noncomputable def kraft (D : WD) : ℝ := (D.map fun p => (1 / 2 : ℝ) ^ p.2).sum

/-- The multiset of weights. -/
