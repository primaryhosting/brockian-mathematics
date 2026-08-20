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

def PrefixFreeMultiset (V : Multiset (List Bool)) : Prop :=
  V.Nodup ∧ ∀ u ∈ V, ∀ v ∈ V, u ≠ v → ¬ u <+: v

/-- Expected codeword length of a multiset of (weight, codeword) pairs. -/
