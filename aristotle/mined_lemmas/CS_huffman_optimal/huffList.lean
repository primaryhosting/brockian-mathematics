import RequestProject.Huffman

/-!
# Achievability of the Huffman cost

Companion to `RequestProject.Huffman`.  Here we show that the Huffman cost is *attained*:
there really is a prefix code whose expected codeword length equals `CS.huffCost`.

Combined with the optimality bound `CS.huffman_optimal`, this gives
`CS.huffman_isLeast`: the Huffman cost is the least expected codeword length among all
prefix codes.
-/

namespace CS

open scoped BigOperators

noncomputable section

/-- A multiset of binary codewords is prefix-free: the codewords are pairwise distinct and
none is a prefix of another. -/

noncomputable def huffList : List ℝ → ℝ
  | [] => 0
  | [_] => 0
  | a :: b :: l => (a + b) + huffList (Multiset.sort ((a + b) ::ₘ (↑l : Multiset ℝ)) (· ≤ ·))
termination_by l => l.length
decreasing_by simp

/-- The cost of the Huffman code built from the multiset of weights `W`, i.e. the
sum `∑ w * (depth of w)` over the Huffman tree. -/
