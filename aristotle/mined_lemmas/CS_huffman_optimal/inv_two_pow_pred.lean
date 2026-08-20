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

theorem inv_two_pow_pred (d : ℕ) (hd : 1 ≤ d) :
    ((2:ℝ)⁻¹) ^ (d - 1) = 2 * ((2:ℝ)⁻¹) ^ d := by
  have h : ((2:ℝ)⁻¹) ^ d = ((2:ℝ)⁻¹) ^ (d - 1) * (2:ℝ)⁻¹ := by
    rw [← pow_succ]
    congr 1
    omega
  rw [h]
  ring

/-- If the maximum length `d ≥ 1` is attained by exactly one codeword, then that codeword
can be shortened while keeping the Kraft inequality. -/
