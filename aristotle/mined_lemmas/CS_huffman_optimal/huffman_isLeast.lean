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

theorem huffman_isLeast {α : Type*} [Fintype α] (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) :
    IsLeast {r : ℝ | ∃ c : α → List Bool, IsPrefixCode c ∧ ∑ a, w a * ((c a).length : ℝ) = r}
      (huffCost (Multiset.map w Finset.univ.val)) := by
  constructor
  · obtain ⟨c, hc, hcost⟩ := huffman_achievable w
    exact ⟨c, hc, hcost⟩
  · rintro r ⟨c, hc, rfl⟩
    exact huffman_optimal w hw c hc

end

end CS

import Mathlib

/-!
# Optimality of Huffman coding

This file develops, from scratch, a proof that Huffman coding minimizes the expected
codeword length among all prefix (prefix-free) binary codes.

The development has three parts.

* `CS.huffCost` : the cost of the Huffman code for a multiset of weights, defined by the
  usual greedy algorithm (repeatedly merge the two smallest weights, and accumulate the
  merged weights).
* `CS.huffCost_le_of_kraft` : the core optimality statement.  For any assignment of
  codeword *lengths* to the weights whose Kraft sum `∑ 2 ^ (-ℓ)` is at most `1`, the
  Huffman cost is a lower bound for the resulting expected length.
* `CS.kraft_le_one_of_prefixFree` : Kraft's inequality: the lengths of a prefix-free code
  satisfy the Kraft inequality.

Combining the last two yields `CS.huffman_optimal`.
-/

namespace CS

open scoped BigOperators

noncomputable section

/-! ## The Huffman cost -/

/-- Auxiliary: the Huffman cost of a *sorted* list of weights.  At each step the two
smallest weights `a ≤ b` are merged into `a + b`, contributing `a + b` to the cost. -/
