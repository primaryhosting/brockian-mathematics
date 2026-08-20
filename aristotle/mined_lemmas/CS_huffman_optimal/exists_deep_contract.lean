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

lemma exists_deep_contract (t : HTree) (h : 1 ≤ maxDepth t) :
    ∃ (x y : ℝ) (M : Multiset (ℝ × ℕ)),
      leavesD t = (x, maxDepth t) ::ₘ (y, maxDepth t) ::ₘ M ∧
      ∀ c : ℝ, ∃ s : HTree, leavesD s = (c, maxDepth t - 1) ::ₘ M := by
  induction t with
  | leaf w => simp [maxDepth] at h
  | node l r ihl ihr =>
      by_cases hle : maxDepth r ≤ maxDepth l
      · have hm : maxDepth (node l r) = maxDepth l + 1 := by simp only [maxDepth]; omega
        rcases Nat.eq_zero_or_pos (maxDepth l) with h0 | h1
        · obtain ⟨u, rfl⟩ := eq_leaf_of_maxDepth_zero h0
          have hr0 : maxDepth r = 0 := by omega
          obtain ⟨v, rfl⟩ := eq_leaf_of_maxDepth_zero hr0
          refine ⟨u, v, 0, ?_, fun c => ⟨leaf c, ?_⟩⟩
          · simp [leavesD_node, maxDepth]
          · simp [maxDepth]
        · obtain ⟨x, y, M, hM, hc⟩ := ihl h1
          refine ⟨x, y, M.map (fun p => (p.1, p.2 + 1))
            + (leavesD r).map (fun p => (p.1, p.2 + 1)), ?_, ?_⟩
          · rw [leavesD_node, hM, hm]
            simp only [Multiset.map_cons, Multiset.cons_add]
          · intro c
            obtain ⟨sl, hsl⟩ := hc c
            refine ⟨node sl r, ?_⟩
            have hd : maxDepth l - 1 + 1 = maxDepth (node l r) - 1 := by omega
            rw [leavesD_node, hsl]
            simp only [Multiset.map_cons, Multiset.cons_add, hd]
      · have hm : maxDepth (node l r) = maxDepth r + 1 := by simp only [maxDepth]; omega
        have h1 : 1 ≤ maxDepth r := by omega
        obtain ⟨x, y, M, hM, hc⟩ := ihr h1
        refine ⟨x, y, (leavesD l).map (fun p => (p.1, p.2 + 1))
          + M.map (fun p => (p.1, p.2 + 1)), ?_, ?_⟩
        · rw [leavesD_node, hM, hm]
          simp only [Multiset.map_cons, Multiset.add_cons]
        · intro c
          obtain ⟨sr, hsr⟩ := hc c
          refine ⟨node l sr, ?_⟩
          have hd : maxDepth r - 1 + 1 = maxDepth (node l r) - 1 := by omega
          rw [leavesD_node, hsr]
          simp only [Multiset.map_cons, Multiset.add_cons, hd]

/-! ## Raising one leaf weight -/

/-- If the multiset of weights of `t` becomes `B` after replacing one occurrence of the
small value `a` by the larger value `x`, then there is a tree with weight multiset `B`
whose cost exceeds that of `t` by at most `m * (x - a)`, where `m` bounds all depths. -/
