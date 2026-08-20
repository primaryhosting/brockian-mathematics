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

lemma codes_isPrefixCode (t : HTree) : IsPrefixCode ((codes t).map Prod.snd) := by
  induction t with
  | leaf w => simp [codes, IsPrefixCode]
  | node l r ihl ihr =>
      simp only [IsPrefixCode, codes, List.map_append, List.map_map, Function.comp_def,
        List.pairwise_append] at *
      refine ⟨?_, ?_, ?_⟩
      · rw [List.pairwise_map] at ihl ⊢
        refine ihl.imp ?_
        intro u v huv
        constructor
        · intro hp; exact huv.1 (by simpa [List.cons_prefix_cons] using hp)
        · intro hp; exact huv.2 (by simpa [List.cons_prefix_cons] using hp)
      · rw [List.pairwise_map] at ihr ⊢
        refine ihr.imp ?_
        intro u v huv
        constructor
        · intro hp; exact huv.1 (by simpa [List.cons_prefix_cons] using hp)
        · intro hp; exact huv.2 (by simpa [List.cons_prefix_cons] using hp)
      · intro u hu v hv
        simp only [List.mem_map] at hu hv
        obtain ⟨p, -, rfl⟩ := hu
        obtain ⟨q, -, rfl⟩ := hv
        constructor
        · intro hp; simp [List.cons_prefix_cons] at hp
        · intro hp; simp [List.cons_prefix_cons] at hp

/-- Prefix-freeness of a weighted code. -/
