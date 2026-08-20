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

lemma hcost_le : ∀ (ws : List ℝ), ws.Pairwise (· ≤ ·) → ∀ t : HTree,
    weights t = (ws : Multiset ℝ) → hcost ws ≤ cost t := by
  intro ws
  induction ws using hcost.induct with
  | case1 =>
      intro _ t ht
      exfalso
      have h0 : weights t = 0 := by simpa using ht
      rw [weights] at h0
      exact leavesD_ne_zero t (Multiset.map_eq_zero.1 h0)
  | case2 a =>
      intro _ t ht
      have hcard : Multiset.card (leavesD t) = 1 := by
        have h1 : Multiset.card (weights t) = 1 := by rw [ht]; simp
        rwa [weights, Multiset.card_map] at h1
      have hmd : maxDepth t = 0 := by
        by_contra hcon
        have := two_le_card_leavesD (t := t) (by omega)
        omega
      obtain ⟨w, rfl⟩ := eq_leaf_of_maxDepth_zero hmd
      simp [hcost]
  | case3 a b rest ih =>
      intro hs t ht
      rw [List.pairwise_cons] at hs
      obtain ⟨ha, hs2⟩ := hs
      have hab : a ≤ b := ha b (by simp)
      have hs3 := hs2
      rw [List.pairwise_cons] at hs3
      obtain ⟨hb, hrestp⟩ := hs3
      have hrest : ∀ z ∈ (rest : Multiset ℝ), b ≤ z := by
        intro z hz
        exact hb z (by simpa using hz)
      have ht' : weights t = a ::ₘ b ::ₘ (rest : Multiset ℝ) := by
        rw [ht]; simp [Multiset.cons_coe]
      obtain ⟨s, hsw, hsc⟩ := exists_merge t a b (rest : Multiset ℝ) ht' hab hrest
      have hsorted : (List.orderedInsert (· ≤ ·) (a + b) rest).Pairwise (· ≤ ·) :=
        List.Pairwise.orderedInsert _ _ hrestp
      have hcoe : ((List.orderedInsert (· ≤ ·) (a + b) rest : List ℝ) : Multiset ℝ)
          = (a + b) ::ₘ (rest : Multiset ℝ) := by
        rw [Multiset.coe_eq_coe.2 (List.perm_orderedInsert _ _ _), Multiset.cons_coe]
      have hle := ih hsorted s (by rw [hsw, hcoe])
      rw [hcost]
      linarith

