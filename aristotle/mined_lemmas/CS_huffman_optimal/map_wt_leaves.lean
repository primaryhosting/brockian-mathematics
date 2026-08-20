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

lemma map_wt_leaves (l : List ℝ) : ((l.map HTree.leaf)).map wt = l := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, wt]

/-! ## Prefix codes

A binary prefix code is a list of codewords (finite bit strings), no one of which is a
prefix of another.  Below, a *weighted code* is a list of pairs `(weight, codeword)` and
its expected codeword length is `∑ weight * (length of codeword)`. -/

/-- A list of codewords is a prefix code if no codeword is a prefix of another. -/
