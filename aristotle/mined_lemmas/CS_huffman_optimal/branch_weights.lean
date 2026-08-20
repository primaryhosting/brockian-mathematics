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

lemma branch_weights : ∀ L : List (ℝ × List Bool), (∀ p ∈ L, p.2 ≠ []) →
    (((branch false L).map Prod.fst : List ℝ) : Multiset ℝ)
      + (((branch true L).map Prod.fst : List ℝ) : Multiset ℝ)
      = ((L.map Prod.fst : List ℝ) : Multiset ℝ) := by
  intro L
  induction L with
  | nil => simp
  | cons p L ih =>
      intro h
      obtain ⟨w, c⟩ := p
      cases c with
      | nil => exact absurd rfl (h (w, []) (by simp))
      | cons d c =>
          have ih' := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
          cases d
          · rw [branch_cons, branch_cons, if_pos rfl, if_neg (by simp)]
            simp only [List.map_cons, ← Multiset.cons_coe, Multiset.cons_add, ih']
          · rw [branch_cons, branch_cons, if_neg (by simp), if_pos rfl]
            simp only [List.map_cons, ← Multiset.cons_coe, Multiset.add_cons, ih']

