import RequestProject.HuffmanKraft

/-!
# Weighted depth multisets, the Huffman merging process, and the optimality bound
-/

namespace CS

/-- A *weighted depth multiset*: a finite multiset of pairs `(weight, codeword length)`. -/
abbrev WD := Multiset (ℝ × ℕ)

/-- The expected codeword length associated to a weighted depth multiset. -/

def allLists : ℕ → Finset (List Bool)
  | 0 => {[]}
  | n + 1 => Finset.image (fun p : Bool × List Bool => p.1 :: p.2)
      (Finset.univ ×ˢ allLists n)

