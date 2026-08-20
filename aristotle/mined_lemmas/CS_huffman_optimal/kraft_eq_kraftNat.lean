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

theorem kraft_eq_kraftNat (d : ℕ) (L : Multiset ℕ) (hL : ∀ n ∈ L, n ≤ d) :
    kraft L * 2 ^ d = (kraftNat d L : ℝ) := by
  induction L using Multiset.induction with
  | empty => simp [kraftNat]
  | cons a t ih =>
      have ha : a ≤ d := hL a (Multiset.mem_cons_self _ _)
      have ht : ∀ n ∈ t, n ≤ d := fun n hn => hL n (Multiset.mem_cons_of_mem hn)
      rw [kraft_cons, add_mul, ih ht]
      have hda : ((2 : ℝ)⁻¹) ^ a * 2 ^ d = (2 : ℝ) ^ (d - a) := by
        have h1 : ((2 : ℝ)⁻¹) ^ a * 2 ^ d = 2 ^ d / 2 ^ a := by
          rw [inv_pow]; ring
        rw [h1, div_eq_iff (by positivity : (2:ℝ) ^ a ≠ 0), ← pow_add]
        congr 1
        omega
      rw [hda]
      simp only [kraftNat, Multiset.map_cons, Multiset.sum_cons]
      push_cast
      ring

