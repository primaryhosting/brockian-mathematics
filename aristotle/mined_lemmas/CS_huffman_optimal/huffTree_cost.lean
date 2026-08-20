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

lemma huffTree_cost : ∀ (L : List HTree), L ≠ [] →
    cost (huffTree L) = (L.map cost).sum + hcost (L.map wt) := by
  intro L
  induction L using huffTree.induct with
  | case1 => intro h; exact absurd rfl h
  | case2 t => intro _; simp [huffTree, hcost]
  | case3 t u rest ih =>
      intro _
      have hperm := List.perm_orderedInsert (fun a b : HTree => wt a ≤ wt b) (node t u) rest
      rw [huffTree, ih (orderedInsert_ne_nil (node t u) rest), (hperm.map cost).sum_eq,
        map_wt_orderedInsert]
      simp only [List.map_cons, List.sum_cons, cost_node, wt_node, hcost]
      ring

/-- Optimality of the numerical Huffman cost. -/
