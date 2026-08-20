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

theorem huffman_optimal_tree (ws : List ℝ) (hne : ws ≠ []) :
    weights (huffman ws) = (ws : Multiset ℝ) ∧
      ∀ t : HTree, weights t = (ws : Multiset ℝ) → cost (huffman ws) ≤ cost t := by
  have hperm : (List.insertionSort (· ≤ ·) ws).Perm ws := List.perm_insertionSort _ _
  have hcoe : ((List.insertionSort (· ≤ ·) ws : List ℝ) : Multiset ℝ) = (ws : Multiset ℝ) :=
    Multiset.coe_eq_coe.2 hperm
  have hsne : (List.insertionSort (· ≤ ·) ws) ≠ [] := by
    intro hcon
    apply hne
    have hlen := hperm.length_eq
    rw [hcon] at hlen
    exact List.eq_nil_of_length_eq_zero hlen.symm
  have hmne : ((List.insertionSort (· ≤ ·) ws).map HTree.leaf) ≠ [] := by
    simpa using hsne
  refine ⟨?_, ?_⟩
  · rw [huffman, huffTree_leaves _ hmne, sum_weights_leaves, hcoe]
  · intro t ht
    rw [huffman, huffTree_cost _ hmne, sum_cost_leaves, map_wt_leaves, zero_add]
    exact hcost_le _ (List.pairwise_insertionSort _ _) t (by rw [ht, ← hcoe])

/-- **Huffman coding is optimal: it minimizes the expected codeword length among all
binary prefix codes.**

Given a nonempty list `ws` of nonnegative symbol weights (e.g. probabilities), the
Huffman code `codes (huffman ws)` assigns a binary codeword to each symbol so that

* the multiset of weights it encodes is exactly `ws`;
* it is a prefix code (no codeword is a prefix of another);
* its expected codeword length `∑ weight * (length of codeword)` is less than or equal to
  that of *every* prefix code for the same multiset of weights. -/
