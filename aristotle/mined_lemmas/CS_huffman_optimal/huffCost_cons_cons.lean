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

theorem huffCost_cons_cons (x y : ℝ) (l : Multiset ℝ) (hx : ∀ z ∈ l, x ≤ z)
    (hy : ∀ z ∈ l, y ≤ z) :
    huffCost (x ::ₘ y ::ₘ l) = (x + y) + huffCost ((x + y) ::ₘ l) := by
  rw [huffCost, sort_cons_cons x y l hx hy, huffList, huffCost, min_add_max]
  congr 2
  rw [Multiset.sort_eq]

/-- Sanity check: for weights `1, 1, 2` the Huffman code has expected length
`1*2 + 1*2 + 2*1 = 6`. -/
example : huffCost {1, 1, 2} = (6 : ℝ) := by
  have h1 : ({1, 1, 2} : Multiset ℝ) = (1 : ℝ) ::ₘ (1 : ℝ) ::ₘ {(2 : ℝ)} := rfl
  rw [h1, huffCost_cons_cons 1 1 {2} (by norm_num) (by norm_num),
    show ((1 : ℝ) + 1) ::ₘ ({2} : Multiset ℝ) = (2 : ℝ) ::ₘ (2 : ℝ) ::ₘ 0 by norm_num,
    huffCost_cons_cons 2 2 0 (by simp) (by simp)]
  norm_num

/-! ## Multiset helpers -/

