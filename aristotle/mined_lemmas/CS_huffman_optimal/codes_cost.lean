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

lemma codes_cost (t : HTree) : codeCost (codes t) = cost t := by
  induction t with
  | leaf w => simp [codes, codeCost]
  | node l r ihl ihr =>
      simp only [codes, codeCost, List.map_append, List.sum_append]
      rw [show ((List.map (fun p => (p.1, false :: p.2)) (codes l)).map
            (fun p => p.1 * (p.2.length : ℝ))).sum = codeCost
            ((codes l).map (fun p => (p.1, false :: p.2))) from rfl,
        show ((List.map (fun p => (p.1, true :: p.2)) (codes r)).map
            (fun p => p.1 * (p.2.length : ℝ))).sum = codeCost
            ((codes r).map (fun p => (p.1, true :: p.2))) from rfl,
        codeCost_map_cons, codeCost_map_cons, ihl, ihr, codes_weight_sum, codes_weight_sum,
        cost_node]
      ring

