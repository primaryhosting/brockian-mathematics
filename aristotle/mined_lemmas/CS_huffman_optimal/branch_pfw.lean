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

lemma branch_pfw (b : Bool) : ∀ L : List (ℝ × List Bool), PFW L → PFW (branch b L) := by
  intro L
  induction L with
  | nil => intro _; simp [PFW]
  | cons p L ih =>
      intro h
      rw [PFW, List.pairwise_cons] at h
      obtain ⟨hh, ht⟩ := h
      obtain ⟨w, c⟩ := p
      cases c with
      | nil => simpa using ih ht
      | cons d c =>
          rw [branch_cons]
          by_cases hd : d = b
          · subst hd
            rw [if_pos rfl, PFW, List.pairwise_cons]
            refine ⟨?_, ih ht⟩
            intro y hy
            have hmem := branch_mem hy
            have hy2 := hh _ hmem
            constructor
            · intro hp; exact hy2.1 (by simpa [List.cons_prefix_cons] using hp)
            · intro hp; exact hy2.2 (by simpa [List.cons_prefix_cons] using hp)
          · rw [if_neg hd]; exact ih ht

