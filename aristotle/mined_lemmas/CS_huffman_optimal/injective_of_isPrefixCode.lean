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

theorem injective_of_isPrefixCode {α : Type*} {c : α → List Bool} (hc : IsPrefixCode c) :
    Function.Injective c := by
  intro a b hab
  by_contra hne
  exact hc a b hne (by rw [hab])

/-- Kraft's inequality, in terms of a prefix code indexed by a finite type. -/
