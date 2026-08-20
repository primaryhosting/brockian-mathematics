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

def PrefixFreeSet (C : Finset (List Bool)) : Prop :=
  ∀ l ∈ C, ∀ m ∈ C, l ≠ m → ¬ (l <+: m)

/-- **Kraft's inequality** for a prefix-free set of binary codewords. -/
