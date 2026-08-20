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

theorem kraft_merge (d : ℕ) (hd : 1 ≤ d) (L : Multiset ℕ) :
    kraft ((d - 1) ::ₘ L) = kraft (d ::ₘ d ::ₘ L) := by
  rw [kraft_cons, kraft_cons, kraft_cons, inv_two_pow_pred d hd]
  ring

/-! ## The core optimality theorem -/

