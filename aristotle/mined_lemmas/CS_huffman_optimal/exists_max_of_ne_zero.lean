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

theorem exists_max_of_ne_zero {α : Type*} [LinearOrder α] (s : Multiset α) (h : s ≠ 0) :
    ∃ x ∈ s, ∀ y ∈ s, y ≤ x := by
  induction s using Multiset.induction with
  | empty => exact absurd rfl h
  | cons a t ih =>
      by_cases ht : t = 0
      · subst ht; exact ⟨a, by simp, by simp⟩
      · obtain ⟨x, hx, hx'⟩ := ih ht
        rcases le_total a x with hax | hax
        · exact ⟨x, Multiset.mem_cons_of_mem hx, by
            intro y hy
            rcases Multiset.mem_cons.1 hy with rfl | hy
            · exact hax
            · exact hx' y hy⟩
        · exact ⟨a, by simp, by
            intro y hy
            rcases Multiset.mem_cons.1 hy with rfl | hy
            · exact le_rfl
            · exact (hx' y hy).trans hax⟩

/-! ## The exchange (swap) argument -/

/-- If some element of `S` has (maximal) length `d` and `x` is a minimal weight occurring in
`S`, then `S` can be rearranged, without changing the multiset of weights or of lengths and
without increasing the cost, so that the weight `x` sits at length `d`. -/
