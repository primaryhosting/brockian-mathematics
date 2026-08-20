import RequestProject.HuffmanKraft

/-!
# Weighted depth multisets, the Huffman merging process, and the optimality bound
-/

namespace CS

/-- A *weighted depth multiset*: a finite multiset of pairs `(weight, codeword length)`. -/
abbrev WD := Multiset (ℝ × ℕ)

/-- The expected codeword length associated to a weighted depth multiset. -/

theorem kraft_eq_kn (M : ℕ) (D : WD) (h : ∀ p ∈ D, p.2 ≤ M) :
    kraft D * 2 ^ M = (kn M D : ℝ) := by
  induction D using Multiset.induction with
  | empty => simp
  | cons a D ih =>
    have ha : a.2 ≤ M := h a (Multiset.mem_cons_self _ _)
    have ih' := ih fun p hp => h p (Multiset.mem_cons_of_mem hp)
    have hsplit : (2 : ℝ) ^ M = 2 ^ (M - a.2) * 2 ^ a.2 := by
      rw [← pow_add]; congr 1; omega
    rw [kn_cons, kraft_cons, add_mul, ih']
    push_cast
    rw [hsplit]
    have : (1 / 2 : ℝ) ^ a.2 * (2 ^ (M - a.2) * 2 ^ a.2) = 2 ^ (M - a.2) := by
      rw [mul_comm ((2:ℝ) ^ (M - a.2)), ← mul_assoc, ← mul_pow]
      norm_num
    rw [this]

