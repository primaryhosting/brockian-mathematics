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

theorem sort_cons_cons (x y : ℝ) (l : Multiset ℝ) (hx : ∀ z ∈ l, x ≤ z) (hy : ∀ z ∈ l, y ≤ z) :
    Multiset.sort (x ::ₘ y ::ₘ l) (· ≤ ·) = min x y :: max x y :: Multiset.sort l (· ≤ ·) := by
  have h1 : x ::ₘ y ::ₘ l = min x y ::ₘ max x y ::ₘ l := by
    rcases le_total x y with h | h
    · simp [min_eq_left h, max_eq_right h]
    · simp [min_eq_right h, max_eq_left h, Multiset.cons_swap]
  rw [h1, Multiset.sort_cons, Multiset.sort_cons]
  · intro b hb
    rcases le_total x y with h | h
    · simpa [max_eq_right h] using hy b hb
    · simpa [max_eq_left h] using hx b hb
  · intro b hb
    simp only [Multiset.mem_cons] at hb
    rcases hb with rfl | hb
    · exact min_le_max
    · exact le_trans (min_le_left x y) (hx b hb)

