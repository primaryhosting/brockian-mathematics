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

lemma exists_repl (t : HTree) (v v' : ℝ) (d : ℕ) (M : Multiset (ℝ × ℕ))
    (h : leavesD t = (v, d) ::ₘ M) : ∃ s : HTree, leavesD s = (v', d) ::ₘ M := by
  induction t generalizing v d M with
  | leaf w =>
      rw [leavesD_leaf, Multiset.singleton_eq_cons_iff] at h
      obtain ⟨h1, h2⟩ := h
      refine ⟨leaf v', ?_⟩
      have hd : d = 0 := by simpa using congrArg Prod.snd h1.symm
      simp [h2, hd]
  | node l r ihl ihr =>
      have hmem : (v, d) ∈ leavesD (node l r) := by rw [h]; exact Multiset.mem_cons_self _ _
      rw [leavesD_node] at hmem h
      rcases Multiset.mem_add.1 hmem with hl | hr
      · obtain ⟨⟨a, dq⟩, hq, hqe⟩ := Multiset.mem_map.1 hl
        simp only [Prod.mk.injEq] at hqe
        obtain ⟨rfl, rfl⟩ := hqe
        obtain ⟨Ml, hMl⟩ := Multiset.exists_cons_of_mem hq
        rw [hMl] at h
        simp only [Multiset.map_cons, Multiset.cons_add] at h
        have hMeq := (Multiset.cons_inj_right (a, dq + 1)).1 h
        obtain ⟨sl, hsl⟩ := ihl a dq Ml hMl
        refine ⟨node sl r, ?_⟩
        simp only [leavesD_node, hsl, Multiset.map_cons, Multiset.cons_add, hMeq]
      · obtain ⟨⟨a, dq⟩, hq, hqe⟩ := Multiset.mem_map.1 hr
        simp only [Prod.mk.injEq] at hqe
        obtain ⟨rfl, rfl⟩ := hqe
        obtain ⟨Mr, hMr⟩ := Multiset.exists_cons_of_mem hq
        rw [hMr] at h
        simp only [Multiset.map_cons, Multiset.add_cons] at h
        have hMeq := (Multiset.cons_inj_right (a, dq + 1)).1 h
        obtain ⟨sr, hsr⟩ := ihr a dq Mr hMr
        refine ⟨node l sr, ?_⟩
        simp only [leavesD_node, hsr, Multiset.map_cons, Multiset.add_cons, hMeq]

/-! ## Contracting a deepest pair of sibling leaves -/

/-- Any tree of positive depth has two sibling leaves at maximal depth; moreover the
subtree consisting of those two leaves may be replaced by a single leaf carrying an
arbitrary weight `c`, which then sits at depth `maxDepth t - 1`. -/
