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

theorem huffCost_le_of_kraft (S : Multiset (ℝ × ℕ)) (hpos : ∀ p ∈ S, 0 ≤ p.1)
    (hk : kraft (S.map Prod.snd) ≤ 1) : huffCost (S.map Prod.fst) ≤ costOf S :=
  huffCost_le_of_kraft_aux _ S rfl hpos hk

/-! ## Kraft's inequality for prefix-free codes -/

/-- A finite set of binary words is prefix-free if no word is a prefix of another. -/
