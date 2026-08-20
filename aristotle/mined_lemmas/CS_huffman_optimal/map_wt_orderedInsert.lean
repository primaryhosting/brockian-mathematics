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

lemma map_wt_orderedInsert (x : HTree) (L : List HTree) :
    (List.orderedInsert (fun a b : HTree => wt a ≤ wt b) x L).map wt
      = List.orderedInsert (· ≤ ·) (wt x) (L.map wt) := by
  induction L with
  | nil => simp [List.orderedInsert]
  | cons u us ih =>
      by_cases h : wt x ≤ wt u
      · simp [List.orderedInsert, h]
      · simp [List.orderedInsert, h, ih]

