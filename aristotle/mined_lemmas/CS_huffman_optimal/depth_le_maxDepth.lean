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

lemma depth_le_maxDepth {t : HTree} {p : ℝ × ℕ} (h : p ∈ leavesD t) : p.2 ≤ maxDepth t := by
  induction t generalizing p with
  | leaf w => simp at h; simp [h, maxDepth]
  | node l r ihl ihr =>
      simp only [leavesD_node, Multiset.mem_add, Multiset.mem_map] at h
      rcases h with ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
      · have := ihl hq; simp only [maxDepth]; omega
      · have := ihr hq; simp only [maxDepth]; omega

