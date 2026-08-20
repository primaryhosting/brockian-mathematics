import RequestProject.HuffmanKraft

/-!
# Weighted depth multisets, the Huffman merging process, and the optimality bound
-/

namespace CS

/-- A *weighted depth multiset*: a finite multiset of pairs `(weight, codeword length)`. -/
abbrev WD := Multiset (ℝ × ℕ)

/-- The expected codeword length associated to a weighted depth multiset. -/

theorem PrefixFree.symm : Symmetric fun u v : List Bool => ¬ u <+: v ∧ ¬ v <+: u :=
  fun _ _ hxy => ⟨hxy.2, hxy.1⟩

/-- The finset of all boolean lists of length `n`. -/
