/-
# Huffman Optimal
Category: Computer Science
Target: CS.huffman_optimal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huffman Optimal
Category: Computer Science
Target: CS.huffman_optimal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

/-! ## Binary code trees

A binary code tree is a full binary tree whose leaves carry weights (e.g. symbol
probabilities).  Such a tree is exactly the same thing as a binary prefix code on the
leaf symbols: the codeword of a leaf is the sequence of left/right turns leading to it,
so the length of the codeword of a leaf equals the depth of that leaf.
Consequently the *expected codeword length* of the code is
`∑ (weight of leaf) * (depth of leaf)`, which is the quantity `cost` below. -/

inductive HTree where
  | leaf : ℝ → HTree
  | node : HTree → HTree → HTree
deriving Inhabited

namespace HTree

/-- The multiset of `(weight, depth)` pairs of the leaves of a tree. -/

lemma raise_two {m : ℕ} (t : HTree) (hd : ∀ p ∈ leavesD t, p.2 ≤ m) (B : Multiset ℝ)
    (x y a b : ℝ) (heq : x ::ₘ y ::ₘ weights t = a ::ₘ b ::ₘ B) (hab : a ≤ b) (hax : a ≤ x)
    (hby : b ≤ y) :
    ∃ s : HTree, weights s = B ∧ cost s ≤ cost t + m * (x - a) + m * (y - b) := by
  have hsplit : ∃ B1 : Multiset ℝ, x ::ₘ weights t = a ::ₘ B1 ∧ y ::ₘ B1 = b ::ₘ B := by
    by_cases hax' : a = x
    · refine ⟨weights t, by rw [hax'], ?_⟩
      have h2 : x ::ₘ (y ::ₘ weights t) = x ::ₘ (b ::ₘ B) := by rw [heq, hax']
      exact (Multiset.cons_inj_right x).1 h2
    · have haW : a ∈ weights t := by
        have hmem : a ∈ x ::ₘ y ::ₘ weights t := by rw [heq]; exact Multiset.mem_cons_self _ _
        rcases Multiset.mem_cons.1 hmem with h1 | h1
        · exact absurd h1 hax'
        rcases Multiset.mem_cons.1 h1 with h2 | h2
        · have hba : b ≤ a := by rw [h2]; exact hby
          have hab2 : a = b := le_antisymm hab hba
          rw [← h2, ← hab2] at heq
          have h3 : a ::ₘ (x ::ₘ weights t) = a ::ₘ (a ::ₘ B) := by
            rw [Multiset.cons_swap]; exact heq
          have h4 : x ::ₘ weights t = a ::ₘ B := (Multiset.cons_inj_right a).1 h3
          have h5 : a ∈ x ::ₘ weights t := by rw [h4]; exact Multiset.mem_cons_self _ _
          rcases Multiset.mem_cons.1 h5 with h6 | h6
          · exact absurd h6 hax'
          · exact h6
        · exact h2
      obtain ⟨C, hC⟩ := Multiset.exists_cons_of_mem haW
      refine ⟨x ::ₘ C, ?_, ?_⟩
      · rw [hC, Multiset.cons_swap]
      · have h4 : a ::ₘ (y ::ₘ x ::ₘ C) = a ::ₘ (b ::ₘ B) := by
          rw [← heq, hC]
          simp only [← Multiset.singleton_add]
          abel
        have h5 := (Multiset.cons_inj_right a).1 h4
        rw [← h5, Multiset.cons_swap]
  obtain ⟨B1, h1, h2⟩ := hsplit
  obtain ⟨s1, hs1w, hs1d, hs1c⟩ := raise_step t hd B1 x a h1 hax
  obtain ⟨s2, hs2w, _, hs2c⟩ := raise_step s1 hs1d B y b (by rw [hs1w]; exact h2) hby
  exact ⟨s2, hs2w, by linarith⟩

/-! ## The key exchange lemma -/

/-- If `a` and `b` are two smallest leaf weights of `t`, then there is a tree in which they
have been merged into a single leaf of weight `a + b`, of cost at most `cost t - a - b`. -/
