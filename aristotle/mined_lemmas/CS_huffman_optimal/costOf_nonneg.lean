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

theorem costOf_nonneg {S : Multiset (ℝ × ℕ)} (h : ∀ p ∈ S, 0 ≤ p.1) : 0 ≤ costOf S := by
  refine Multiset.sum_nonneg ?_
  intro x hx
  simp only [Multiset.mem_map] at hx
  obtain ⟨p, hp, rfl⟩ := hx
  exact mul_nonneg (h p hp) (Nat.cast_nonneg _)

/-! ## Basic facts about `huffCost` -/

