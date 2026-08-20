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

lemma raise_step {m : ℕ} (t : HTree) (hd : ∀ p ∈ leavesD t, p.2 ≤ m) (B : Multiset ℝ) (x a : ℝ)
    (heq : x ::ₘ weights t = a ::ₘ B) (hax : a ≤ x) :
    ∃ s : HTree, weights s = B ∧ (∀ p ∈ leavesD s, p.2 ≤ m) ∧ cost s ≤ cost t + m * (x - a) := by
  by_cases hxa : a = x
  · subst hxa
    exact ⟨t, (Multiset.cons_inj_right _).1 heq, hd, by simp⟩
  · have ha : a ∈ x ::ₘ weights t := by rw [heq]; exact Multiset.mem_cons_self _ _
    have ha' : a ∈ weights t := by
      rcases Multiset.mem_cons.1 ha with h1 | h1
      · exact absurd h1 hxa
      · exact h1
    obtain ⟨p, hp, hp1⟩ := Multiset.mem_map.1 ha'
    obtain ⟨M, hM⟩ := Multiset.exists_cons_of_mem hp
    have hd2 : p.2 ≤ m := hd p (by rw [hM]; exact Multiset.mem_cons_self _ _)
    obtain ⟨s, hs⟩ := exists_repl t p.1 x p.2 M (by rw [hM])
    have hCt : weights t = a ::ₘ M.map Prod.fst := by
      rw [weights, hM, Multiset.map_cons, hp1]
    have hB : B = x ::ₘ M.map Prod.fst := by
      have h2 : a ::ₘ (x ::ₘ M.map Prod.fst) = a ::ₘ B := by
        rw [← heq, hCt, Multiset.cons_swap]
      exact ((Multiset.cons_inj_right a).1 h2).symm
    refine ⟨s, ?_, ?_, ?_⟩
    · rw [weights, hs, Multiset.map_cons, hB]
    · intro q hq
      rw [hs] at hq
      rcases Multiset.mem_cons.1 hq with h1 | h1
      · rw [h1]; exact hd2
      · exact hd q (by rw [hM]; exact Multiset.mem_cons_of_mem h1)
    · have hcs : cost s = x * p.2 + costOf M := by rw [cost, hs, costOf_cons]
      have hct : cost t = a * p.2 + costOf M := by rw [cost, hM, costOf_cons, hp1]
      have hpm : (p.2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hd2
      rw [hcs, hct]
      nlinarith [sub_nonneg.2 hax]

/-- Two successive raises. -/
