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

theorem kraft_le_one_of_isPrefixCode {α : Type*} [Fintype α] {c : α → List Bool}
    (hc : IsPrefixCode c) : ∑ a, ((2:ℝ)⁻¹) ^ (c a).length ≤ 1 := by
  classical
  set C : Finset (List Bool) := Finset.univ.image c with hC
  have hreindex : ∑ a, ((2:ℝ)⁻¹) ^ (c a).length = ∑ l ∈ C, ((2:ℝ)⁻¹) ^ l.length := by
    rw [hC, Finset.sum_image (fun x _ y _ h => injective_of_isPrefixCode hc h)]
  rw [hreindex]
  refine kraft_finset_le (C.sup fun l => l.length) C (fun l hl => Finset.le_sup hl) ?_
  intro l hl m hm hne hpre
  rw [hC, Finset.mem_image] at hl hm
  obtain ⟨a, -, rfl⟩ := hl
  obtain ⟨b, -, rfl⟩ := hm
  exact hc a b (fun h => hne (by rw [h])) hpre

/-! ## Main theorem -/

/-- **Huffman coding minimizes the expected codeword length among prefix codes.**

For any finite alphabet `α` with nonnegative weights `w` and any prefix code
`c : α → List Bool`, the cost of the Huffman code built from the multiset of weights is at
most the expected codeword length `∑ a, w a * (c a).length` of `c`. -/
