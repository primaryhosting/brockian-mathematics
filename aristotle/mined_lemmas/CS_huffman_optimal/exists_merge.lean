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

lemma exists_merge (t : HTree) (a b : ℝ) (rest : Multiset ℝ)
    (ht : weights t = a ::ₘ b ::ₘ rest) (hab : a ≤ b) (hrest : ∀ z ∈ rest, b ≤ z) :
    ∃ s : HTree, weights s = (a + b) ::ₘ rest ∧ cost s ≤ cost t - a - b := by
  have hpos : 1 ≤ maxDepth t := by
    rcases Nat.eq_zero_or_pos (maxDepth t) with h0 | h1
    · obtain ⟨w, rfl⟩ := eq_leaf_of_maxDepth_zero h0
      rw [weights_leaf] at ht
      have := congrArg Multiset.card ht
      simp at this
    · exact h1
  obtain ⟨x, y, M, hM, hc⟩ := exists_deep_contract t hpos
  set m := maxDepth t with hmdef
  set A := M.map Prod.fst with hA
  have hW : weights t = x ::ₘ y ::ₘ A := by
    rw [weights, hM, Multiset.map_cons, Multiset.map_cons, hA]
  have heqA : x ::ₘ y ::ₘ A = a ::ₘ b ::ₘ rest := by rw [← hW, ht]
  have hcostt : cost t = x * m + y * m + costOf M := by
    rw [cost, hM, costOf_cons, costOf_cons]; ring
  -- the main argument, for a pair `x' y'` of deepest sibling leaves with `a ≤ x'`, `b ≤ y'`
  have main : ∀ x' y' : ℝ, x' ::ₘ y' ::ₘ A = a ::ₘ b ::ₘ rest →
      cost t = x' * m + y' * m + costOf M → a ≤ x' → b ≤ y' →
      ∃ s : HTree, weights s = (a + b) ::ₘ rest ∧ cost s ≤ cost t - a - b := by
    intro x' y' heqA' hcostt' hax hby
    obtain ⟨t1, ht1⟩ := hc (a + b)
    have hw1 : weights t1 = (a + b) ::ₘ A := by rw [weights, ht1, Multiset.map_cons, hA]
    have hdep : ∀ p ∈ leavesD t1, p.2 ≤ m := by
      intro p hp
      rw [ht1] at hp
      rcases Multiset.mem_cons.1 hp with h1 | h1
      · rw [h1]; exact Nat.sub_le _ _
      · exact depth_le_maxDepth (by
          rw [hM]; exact Multiset.mem_cons_of_mem (Multiset.mem_cons_of_mem h1))
    have heq2 : x' ::ₘ y' ::ₘ weights t1 = a ::ₘ b ::ₘ ((a + b) ::ₘ rest) := by
      rw [hw1]
      calc x' ::ₘ y' ::ₘ (a + b) ::ₘ A = (a + b) ::ₘ (x' ::ₘ y' ::ₘ A) := by
            simp only [← Multiset.singleton_add]; abel
        _ = (a + b) ::ₘ (a ::ₘ b ::ₘ rest) := by rw [heqA']
        _ = a ::ₘ b ::ₘ ((a + b) ::ₘ rest) := by
            simp only [← Multiset.singleton_add]; abel
    obtain ⟨s, hsw, hsc⟩ := raise_two t1 hdep ((a + b) ::ₘ rest) x' y' a b heq2 hab hax hby
    refine ⟨s, hsw, ?_⟩
    have hcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
      have : (1 : ℕ) ≤ m := hpos
      push_cast [Nat.cast_sub this]
      ring
    have hc1 : cost t1 = (a + b) * ((m : ℝ) - 1) + costOf M := by
      rw [cost, ht1, costOf_cons, hcast]
    rw [hc1] at hsc
    have hring : (a + b) * ((m : ℝ) - 1) + costOf M + m * (x' - a) + m * (y' - b)
        = x' * m + y' * m + costOf M - a - b := by ring
    rw [hring] at hsc
    rw [hcostt']
    exact hsc
  -- every leaf weight is at least `a`
  have hmin : ∀ z ∈ a ::ₘ b ::ₘ rest, a ≤ z := by
    intro z hz
    rcases Multiset.mem_cons.1 hz with h1 | h1
    · exact le_of_eq h1.symm
    rcases Multiset.mem_cons.1 h1 with h2 | h2
    · rw [h2]; exact hab
    · exact hab.trans (hrest z h2)
  have hxmem : x ∈ a ::ₘ b ::ₘ rest := by rw [← heqA]; exact Multiset.mem_cons_self _ _
  have hymem : y ∈ a ::ₘ b ::ₘ rest := by
    rw [← heqA]; exact Multiset.mem_cons_of_mem (Multiset.mem_cons_self _ _)
  have hax : a ≤ x := hmin x hxmem
  have hay : a ≤ y := hmin y hymem
  have hb : b ≤ x ∨ b ≤ y := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨hx, hy⟩ := hcon
    have hxa : x = a := by
      rcases Multiset.mem_cons.1 hxmem with h1 | h1
      · exact h1
      rcases Multiset.mem_cons.1 h1 with h2 | h2
      · exact absurd h2 (by intro h; rw [h] at hx; exact lt_irrefl b hx)
      · exact absurd (hrest x h2) (not_le.2 hx)
    have hya : y = a := by
      rcases Multiset.mem_cons.1 hymem with h1 | h1
      · exact h1
      rcases Multiset.mem_cons.1 h1 with h2 | h2
      · exact absurd h2 (by intro h; rw [h] at hy; exact lt_irrefl b hy)
      · exact absurd (hrest y h2) (not_le.2 hy)
    rw [hxa, hya] at heqA
    have h5 : a ::ₘ A = b ::ₘ rest := (Multiset.cons_inj_right a).1 heqA
    have h6 : a ∈ b ::ₘ rest := by rw [← h5]; exact Multiset.mem_cons_self _ _
    have h7 : b ≤ a := by
      rcases Multiset.mem_cons.1 h6 with h8 | h8
      · exact le_of_eq h8.symm
      · exact hrest a h8
    rw [hxa] at hx
    exact absurd h7 (not_le.2 hx)
  rcases hb with hbx | hby
  · refine main y x ?_ ?_ hay hbx
    · rw [Multiset.cons_swap]; exact heqA
    · rw [hcostt]; ring
  · exact main x y heqA hcostt hax hby

end HTree

/-! ## The Huffman algorithm -/

open HTree

noncomputable instance : DecidableRel (fun a b : HTree => wt a ≤ wt b) := Classical.decRel _

/-- Numerical Huffman cost of a (sorted) list of weights. -/
