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
def leavesD : HTree → Multiset (ℝ × ℕ)
  | leaf w => {(w, 0)}
  | node l r =>
      (leavesD l).map (fun p => (p.1, p.2 + 1)) + (leavesD r).map (fun p => (p.1, p.2 + 1))

/-- The multiset of leaf weights of a tree. -/
def weights (t : HTree) : Multiset ℝ := (leavesD t).map Prod.fst

/-- The expected codeword length of the prefix code described by the tree:
the sum of `weight * depth` over all leaves. -/
noncomputable def costOf (M : Multiset (ℝ × ℕ)) : ℝ := (M.map (fun p => p.1 * (p.2 : ℝ))).sum

/-- The expected codeword length of the prefix code described by the tree. -/
noncomputable def cost (t : HTree) : ℝ := costOf (leavesD t)

/-- Total weight of a tree. -/
def wt : HTree → ℝ
  | leaf w => w
  | node l r => wt l + wt r

/-- The depth of the deepest leaf. -/
def maxDepth : HTree → ℕ
  | leaf _ => 0
  | node l r => max (maxDepth l) (maxDepth r) + 1

@[simp] lemma leavesD_leaf (w : ℝ) : leavesD (leaf w) = {(w, 0)} := rfl

@[simp] lemma leavesD_node (l r : HTree) :
    leavesD (node l r) =
      (leavesD l).map (fun p => (p.1, p.2 + 1)) + (leavesD r).map (fun p => (p.1, p.2 + 1)) :=
  rfl

@[simp] lemma costOf_zero : costOf 0 = 0 := by simp [costOf]

@[simp] lemma costOf_cons (p : ℝ × ℕ) (M : Multiset (ℝ × ℕ)) :
    costOf (p ::ₘ M) = p.1 * p.2 + costOf M := by simp [costOf]

@[simp] lemma costOf_add (M N : Multiset (ℝ × ℕ)) : costOf (M + N) = costOf M + costOf N := by
  simp [costOf]

@[simp] lemma cost_leaf (w : ℝ) : cost (leaf w) = 0 := by simp [cost, costOf]

@[simp] lemma weights_leaf (w : ℝ) : weights (leaf w) = {w} := rfl

lemma leavesD_ne_zero (t : HTree) : leavesD t ≠ 0 := by
  induction t with
  | leaf w => simp
  | node l r ihl _ =>
      simp only [leavesD_node]
      intro h
      exact ihl (by simpa using (Multiset.map_eq_zero).1 ((add_eq_zero_iff_of_nonneg
        (Multiset.zero_le _) (Multiset.zero_le _)).1 h).1)

lemma depth_le_maxDepth {t : HTree} {p : ℝ × ℕ} (h : p ∈ leavesD t) : p.2 ≤ maxDepth t := by
  induction t generalizing p with
  | leaf w => simp at h; simp [h, maxDepth]
  | node l r ihl ihr =>
      simp only [leavesD_node, Multiset.mem_add, Multiset.mem_map] at h
      rcases h with ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
      · have := ihl hq; simp only [maxDepth]; omega
      · have := ihr hq; simp only [maxDepth]; omega

lemma eq_leaf_of_maxDepth_zero {t : HTree} (h : maxDepth t = 0) : ∃ w, t = leaf w := by
  cases t with
  | leaf w => exact ⟨w, rfl⟩
  | node l r => simp [maxDepth] at h

/-! ## Replacing the value of one leaf -/

/-- We may change the weight sitting at any one leaf, keeping all depths. -/
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
lemma raise_step {m : ℕ} (t : HTree) (hd : ∀ p ∈ leavesD t, p.2 ≤ m) (B : Multiset ℝ) (x a : ℝ)
    (heq : x ::ₘ weights t = a ::ₘ B) (hax : a ≤ x) :
    ∃ s : HTree, weights s = B ∧ (∀ p ∈ leavesD s, p.2 ≤ m) ∧ cost s ≤ cost t + m * (x - a) := by
  by_cases hxa : a = x
  · subst hxa
    exact ⟨t, (Multiset.cons_inj_right _).1 heq, hd, by simp⟩
  · have ha : a ∈ x ::ₘ weights t := by rw [heq]; exact Multiset.mem_cons_self _ _
    have ha' : a ∈ weights t := by
      rcases Multiset.mem_cons.1 ha with h1 | h1
      · exact absurd h1 hxa
      · exact h1
    obtain ⟨p, hp, hp1⟩ := Multiset.mem_map.1 ha'
    obtain ⟨M, hM⟩ := Multiset.exists_cons_of_mem hp
    have hd2 : p.2 ≤ m := hd p (by rw [hM]; exact Multiset.mem_cons_self _ _)
    obtain ⟨s, hs⟩ := exists_repl t p.1 x p.2 M (by rw [hM])
    have hCt : weights t = a ::ₘ M.map Prod.fst := by
      rw [weights, hM, Multiset.map_cons, hp1]
    have hB : B = x ::ₘ M.map Prod.fst := by
      have h2 : a ::ₘ (x ::ₘ M.map Prod.fst) = a ::ₘ B := by
        rw [← heq, hCt, Multiset.cons_swap]
      exact ((Multiset.cons_inj_right a).1 h2).symm
    refine ⟨s, ?_, ?_, ?_⟩
    · rw [weights, hs, Multiset.map_cons, hB]
    · intro q hq
      rw [hs] at hq
      rcases Multiset.mem_cons.1 hq with h1 | h1
      · rw [h1]; exact hd2
      · exact hd q (by rw [hM]; exact Multiset.mem_cons_of_mem h1)
    · have hcs : cost s = x * p.2 + costOf M := by rw [cost, hs, costOf_cons]
      have hct : cost t = a * p.2 + costOf M := by rw [cost, hM, costOf_cons, hp1]
      have hpm : (p.2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hd2
      rw [hcs, hct]
      nlinarith [sub_nonneg.2 hax]

/-- Two successive raises. -/
lemma raise_two {m : ℕ} (t : HTree) (hd : ∀ p ∈ leavesD t, p.2 ≤ m) (B : Multiset ℝ)
    (x y a b : ℝ) (heq : x ::ₘ y ::ₘ weights t = a ::ₘ b ::ₘ B) (hab : a ≤ b) (hax : a ≤ x)
    (hby : b ≤ y) :
    ∃ s : HTree, weights s = B ∧ cost s ≤ cost t + m * (x - a) + m * (y - b) := by
  have hsplit : ∃ B1 : Multiset ℝ, x ::ₘ weights t = a ::ₘ B1 ∧ y ::ₘ B1 = b ::ₘ B := by
    by_cases hax' : a = x
    · refine ⟨weights t, by rw [hax'], ?_⟩
      have h2 : x ::ₘ (y ::ₘ weights t) = x ::ₘ (b ::ₘ B) := by rw [heq, hax']
      exact (Multiset.cons_inj_right x).1 h2
    · have haW : a ∈ weights t := by
        have hmem : a ∈ x ::ₘ y ::ₘ weights t := by rw [heq]; exact Multiset.mem_cons_self _ _
        rcases Multiset.mem_cons.1 hmem with h1 | h1
        · exact absurd h1 hax'
        rcases Multiset.mem_cons.1 h1 with h2 | h2
        · have hba : b ≤ a := by rw [h2]; exact hby
          have hab2 : a = b := le_antisymm hab hba
          rw [← h2, ← hab2] at heq
          have h3 : a ::ₘ (x ::ₘ weights t) = a ::ₘ (a ::ₘ B) := by
            rw [Multiset.cons_swap]; exact heq
          have h4 : x ::ₘ weights t = a ::ₘ B := (Multiset.cons_inj_right a).1 h3
          have h5 : a ∈ x ::ₘ weights t := by rw [h4]; exact Multiset.mem_cons_self _ _
          rcases Multiset.mem_cons.1 h5 with h6 | h6
          · exact absurd h6 hax'
          · exact h6
        · exact h2
      obtain ⟨C, hC⟩ := Multiset.exists_cons_of_mem haW
      refine ⟨x ::ₘ C, ?_, ?_⟩
      · rw [hC, Multiset.cons_swap]
      · have h4 : a ::ₘ (y ::ₘ x ::ₘ C) = a ::ₘ (b ::ₘ B) := by
          rw [← heq, hC]
          simp only [← Multiset.singleton_add]
          abel
        have h5 := (Multiset.cons_inj_right a).1 h4
        rw [← h5, Multiset.cons_swap]
  obtain ⟨B1, h1, h2⟩ := hsplit
  obtain ⟨s1, hs1w, hs1d, hs1c⟩ := raise_step t hd B1 x a h1 hax
  obtain ⟨s2, hs2w, _, hs2c⟩ := raise_step s1 hs1d B y b (by rw [hs1w]; exact h2) hby
  exact ⟨s2, hs2w, by linarith⟩

/-! ## The key exchange lemma -/

/-- If `a` and `b` are two smallest leaf weights of `t`, then there is a tree in which they
have been merged into a single leaf of weight `a + b`, of cost at most `cost t - a - b`. -/
lemma exists_merge (t : HTree) (a b : ℝ) (rest : Multiset ℝ)
    (ht : weights t = a ::ₘ b ::ₘ rest) (hab : a ≤ b) (hrest : ∀ z ∈ rest, b ≤ z) :
    ∃ s : HTree, weights s = (a + b) ::ₘ rest ∧ cost s ≤ cost t - a - b := by
  have hpos : 1 ≤ maxDepth t := by
    rcases Nat.eq_zero_or_pos (maxDepth t) with h0 | h1
    · obtain ⟨w, rfl⟩ := eq_leaf_of_maxDepth_zero h0
      rw [weights_leaf] at ht
      have := congrArg Multiset.card ht
      simp at this
    · exact h1
  obtain ⟨x, y, M, hM, hc⟩ := exists_deep_contract t hpos
  set m := maxDepth t with hmdef
  set A := M.map Prod.fst with hA
  have hW : weights t = x ::ₘ y ::ₘ A := by
    rw [weights, hM, Multiset.map_cons, Multiset.map_cons, hA]
  have heqA : x ::ₘ y ::ₘ A = a ::ₘ b ::ₘ rest := by rw [← hW, ht]
  have hcostt : cost t = x * m + y * m + costOf M := by
    rw [cost, hM, costOf_cons, costOf_cons]; ring
  -- the main argument, for a pair `x' y'` of deepest sibling leaves with `a ≤ x'`, `b ≤ y'`
  have main : ∀ x' y' : ℝ, x' ::ₘ y' ::ₘ A = a ::ₘ b ::ₘ rest →
      cost t = x' * m + y' * m + costOf M → a ≤ x' → b ≤ y' →
      ∃ s : HTree, weights s = (a + b) ::ₘ rest ∧ cost s ≤ cost t - a - b := by
    intro x' y' heqA' hcostt' hax hby
    obtain ⟨t1, ht1⟩ := hc (a + b)
    have hw1 : weights t1 = (a + b) ::ₘ A := by rw [weights, ht1, Multiset.map_cons, hA]
    have hdep : ∀ p ∈ leavesD t1, p.2 ≤ m := by
      intro p hp
      rw [ht1] at hp
      rcases Multiset.mem_cons.1 hp with h1 | h1
      · rw [h1]; exact Nat.sub_le _ _
      · exact depth_le_maxDepth (by
          rw [hM]; exact Multiset.mem_cons_of_mem (Multiset.mem_cons_of_mem h1))
    have heq2 : x' ::ₘ y' ::ₘ weights t1 = a ::ₘ b ::ₘ ((a + b) ::ₘ rest) := by
      rw [hw1]
      calc x' ::ₘ y' ::ₘ (a + b) ::ₘ A = (a + b) ::ₘ (x' ::ₘ y' ::ₘ A) := by
            simp only [← Multiset.singleton_add]; abel
        _ = (a + b) ::ₘ (a ::ₘ b ::ₘ rest) := by rw [heqA']
        _ = a ::ₘ b ::ₘ ((a + b) ::ₘ rest) := by
            simp only [← Multiset.singleton_add]; abel
    obtain ⟨s, hsw, hsc⟩ := raise_two t1 hdep ((a + b) ::ₘ rest) x' y' a b heq2 hab hax hby
    refine ⟨s, hsw, ?_⟩
    have hcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
      have : (1 : ℕ) ≤ m := hpos
      push_cast [Nat.cast_sub this]
      ring
    have hc1 : cost t1 = (a + b) * ((m : ℝ) - 1) + costOf M := by
      rw [cost, ht1, costOf_cons, hcast]
    rw [hc1] at hsc
    have hring : (a + b) * ((m : ℝ) - 1) + costOf M + m * (x' - a) + m * (y' - b)
        = x' * m + y' * m + costOf M - a - b := by ring
    rw [hring] at hsc
    rw [hcostt']
    exact hsc
  -- every leaf weight is at least `a`
  have hmin : ∀ z ∈ a ::ₘ b ::ₘ rest, a ≤ z := by
    intro z hz
    rcases Multiset.mem_cons.1 hz with h1 | h1
    · exact le_of_eq h1.symm
    rcases Multiset.mem_cons.1 h1 with h2 | h2
    · rw [h2]; exact hab
    · exact hab.trans (hrest z h2)
  have hxmem : x ∈ a ::ₘ b ::ₘ rest := by rw [← heqA]; exact Multiset.mem_cons_self _ _
  have hymem : y ∈ a ::ₘ b ::ₘ rest := by
    rw [← heqA]; exact Multiset.mem_cons_of_mem (Multiset.mem_cons_self _ _)
  have hax : a ≤ x := hmin x hxmem
  have hay : a ≤ y := hmin y hymem
  have hb : b ≤ x ∨ b ≤ y := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨hx, hy⟩ := hcon
    have hxa : x = a := by
      rcases Multiset.mem_cons.1 hxmem with h1 | h1
      · exact h1
      rcases Multiset.mem_cons.1 h1 with h2 | h2
      · exact absurd h2 (by intro h; rw [h] at hx; exact lt_irrefl b hx)
      · exact absurd (hrest x h2) (not_le.2 hx)
    have hya : y = a := by
      rcases Multiset.mem_cons.1 hymem with h1 | h1
      · exact h1
      rcases Multiset.mem_cons.1 h1 with h2 | h2
      · exact absurd h2 (by intro h; rw [h] at hy; exact lt_irrefl b hy)
      · exact absurd (hrest y h2) (not_le.2 hy)
    rw [hxa, hya] at heqA
    have h5 : a ::ₘ A = b ::ₘ rest := (Multiset.cons_inj_right a).1 heqA
    have h6 : a ∈ b ::ₘ rest := by rw [← h5]; exact Multiset.mem_cons_self _ _
    have h7 : b ≤ a := by
      rcases Multiset.mem_cons.1 h6 with h8 | h8
      · exact le_of_eq h8.symm
      · exact hrest a h8
    rw [hxa] at hx
    exact absurd h7 (not_le.2 hx)
  rcases hb with hbx | hby
  · refine main y x ?_ ?_ hay hbx
    · rw [Multiset.cons_swap]; exact heqA
    · rw [hcostt]; ring
  · exact main x y heqA hcostt hax hby

end HTree

/-! ## The Huffman algorithm -/

open HTree

noncomputable instance : DecidableRel (fun a b : HTree => wt a ≤ wt b) := Classical.decRel _

/-- Numerical Huffman cost of a (sorted) list of weights. -/
noncomputable def hcost : List ℝ → ℝ
  | [] => 0
  | [_] => 0
  | a :: b :: rest => a + b + hcost (List.orderedInsert (· ≤ ·) (a + b) rest)
  termination_by l => l.length
  decreasing_by simp [List.orderedInsert_length]

/-- One step of the Huffman algorithm, on a list of trees sorted by total weight. -/
noncomputable def huffTree : List HTree → HTree
  | [] => leaf 0
  | [t] => t
  | t :: u :: rest =>
      huffTree (List.orderedInsert (fun a b : HTree => wt a ≤ wt b) (node t u) rest)
  termination_by l => l.length
  decreasing_by simp [List.orderedInsert_length]

/-- The Huffman tree of a list of weights. -/
noncomputable def huffman (ws : List ℝ) : HTree :=
  huffTree ((List.insertionSort (· ≤ ·) ws).map HTree.leaf)

lemma wt_eq_sum_weights (t : HTree) : wt t = (weights t).sum := by
  induction t with
  | leaf w => simp [wt, weights]
  | node l r ihl ihr =>
      simp only [wt, weights, leavesD_node, Multiset.map_add, Multiset.sum_add,
        Multiset.map_map, Function.comp] at *
      rw [ihl, ihr]

lemma weights_node (l r : HTree) : weights (node l r) = weights l + weights r := by
  simp [weights, leavesD_node, Multiset.map_map, Function.comp]

lemma costOf_map_succ (M : Multiset (ℝ × ℕ)) :
    costOf (M.map (fun p => (p.1, p.2 + 1))) = costOf M + (M.map Prod.fst).sum := by
  refine Multiset.induction_on M (by simp) ?_
  intro p M ih
  simp only [Multiset.map_cons, costOf_cons, ih, Multiset.sum_cons]
  push_cast
  ring

lemma cost_node (l r : HTree) : cost (node l r) = cost l + cost r + wt l + wt r := by
  simp only [cost, leavesD_node, costOf_add, costOf_map_succ]
  rw [wt_eq_sum_weights l, wt_eq_sum_weights r]
  simp only [weights]
  ring

lemma wt_node (l r : HTree) : wt (node l r) = wt l + wt r := rfl

lemma two_le_card_leavesD {t : HTree} (h : 1 ≤ maxDepth t) : 2 ≤ Multiset.card (leavesD t) := by
  obtain ⟨x, y, M, hM, -⟩ := exists_deep_contract t h
  rw [hM]
  simp only [Multiset.card_cons]
  omega

lemma map_wt_orderedInsert (x : HTree) (L : List HTree) :
    (List.orderedInsert (fun a b : HTree => wt a ≤ wt b) x L).map wt
      = List.orderedInsert (· ≤ ·) (wt x) (L.map wt) := by
  induction L with
  | nil => simp [List.orderedInsert]
  | cons u us ih =>
      by_cases h : wt x ≤ wt u
      · simp [List.orderedInsert, h]
      · simp [List.orderedInsert, h, ih]

lemma orderedInsert_ne_nil (x : HTree) (L : List HTree) :
    List.orderedInsert (fun a b : HTree => wt a ≤ wt b) x L ≠ [] := by
  intro hcon
  have hlen := List.orderedInsert_length (fun a b : HTree => wt a ≤ wt b) L x
  rw [hcon] at hlen
  simp at hlen

lemma huffTree_leaves : ∀ (L : List HTree), L ≠ [] → weights (huffTree L) = (L.map weights).sum := by
  intro L
  induction L using huffTree.induct with
  | case1 => intro h; exact absurd rfl h
  | case2 t => intro _; simp [huffTree]
  | case3 t u rest ih =>
      intro _
      have hperm := List.perm_orderedInsert (fun a b : HTree => wt a ≤ wt b) (node t u) rest
      rw [huffTree, ih (orderedInsert_ne_nil (node t u) rest), (hperm.map weights).sum_eq]
      simp [weights_node, add_assoc]

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
lemma hcost_le : ∀ (ws : List ℝ), ws.Pairwise (· ≤ ·) → ∀ t : HTree,
    weights t = (ws : Multiset ℝ) → hcost ws ≤ cost t := by
  intro ws
  induction ws using hcost.induct with
  | case1 =>
      intro _ t ht
      exfalso
      have h0 : weights t = 0 := by simpa using ht
      rw [weights] at h0
      exact leavesD_ne_zero t (Multiset.map_eq_zero.1 h0)
  | case2 a =>
      intro _ t ht
      have hcard : Multiset.card (leavesD t) = 1 := by
        have h1 : Multiset.card (weights t) = 1 := by rw [ht]; simp
        rwa [weights, Multiset.card_map] at h1
      have hmd : maxDepth t = 0 := by
        by_contra hcon
        have := two_le_card_leavesD (t := t) (by omega)
        omega
      obtain ⟨w, rfl⟩ := eq_leaf_of_maxDepth_zero hmd
      simp [hcost]
  | case3 a b rest ih =>
      intro hs t ht
      rw [List.pairwise_cons] at hs
      obtain ⟨ha, hs2⟩ := hs
      have hab : a ≤ b := ha b (by simp)
      have hs3 := hs2
      rw [List.pairwise_cons] at hs3
      obtain ⟨hb, hrestp⟩ := hs3
      have hrest : ∀ z ∈ (rest : Multiset ℝ), b ≤ z := by
        intro z hz
        exact hb z (by simpa using hz)
      have ht' : weights t = a ::ₘ b ::ₘ (rest : Multiset ℝ) := by
        rw [ht]; simp [Multiset.cons_coe]
      obtain ⟨s, hsw, hsc⟩ := exists_merge t a b (rest : Multiset ℝ) ht' hab hrest
      have hsorted : (List.orderedInsert (· ≤ ·) (a + b) rest).Pairwise (· ≤ ·) :=
        List.Pairwise.orderedInsert _ _ hrestp
      have hcoe : ((List.orderedInsert (· ≤ ·) (a + b) rest : List ℝ) : Multiset ℝ)
          = (a + b) ::ₘ (rest : Multiset ℝ) := by
        rw [Multiset.coe_eq_coe.2 (List.perm_orderedInsert _ _ _), Multiset.cons_coe]
      have hle := ih hsorted s (by rw [hsw, hcoe])
      rw [hcost]
      linarith

lemma sum_weights_leaves (l : List ℝ) :
    (((l.map HTree.leaf)).map weights).sum = (l : Multiset ℝ) := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.map_cons, List.sum_cons, weights_leaf, ih, Multiset.singleton_add,
        Multiset.cons_coe]

lemma sum_cost_leaves (l : List ℝ) : (((l.map HTree.leaf)).map cost).sum = 0 := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, cost_leaf, ih, zero_add]

lemma map_wt_leaves (l : List ℝ) : ((l.map HTree.leaf)).map wt = l := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, wt]

/-! ## Prefix codes

A binary prefix code is a list of codewords (finite bit strings), no one of which is a
prefix of another.  Below, a *weighted code* is a list of pairs `(weight, codeword)` and
its expected codeword length is `∑ weight * (length of codeword)`. -/

/-- A list of codewords is a prefix code if no codeword is a prefix of another. -/
def IsPrefixCode (c : List (List Bool)) : Prop :=
  c.Pairwise (fun u v => ¬ u.IsPrefix v ∧ ¬ v.IsPrefix u)

/-- Expected codeword length of a weighted code. -/
noncomputable def codeCost (c : List (ℝ × List Bool)) : ℝ :=
  (c.map (fun p => p.1 * (p.2.length : ℝ))).sum

@[simp] lemma codeCost_nil : codeCost [] = 0 := rfl

/-- The prefix code described by a tree: the codeword of a leaf is the sequence of turns
(`false` = left, `true` = right) leading to that leaf. -/
def codes : HTree → List (ℝ × List Bool)
  | leaf w => [(w, [])]
  | node l r => (codes l).map (fun p => (p.1, false :: p.2))
      ++ (codes r).map (fun p => (p.1, true :: p.2))

lemma codeCost_map_cons (b : Bool) (c : List (ℝ × List Bool)) :
    codeCost (c.map (fun p => (p.1, b :: p.2))) = codeCost c + (c.map Prod.fst).sum := by
  induction c with
  | nil => simp [codeCost]
  | cons p c ih =>
      simp only [List.map_cons, codeCost, List.sum_cons, List.length_cons] at *
      push_cast
      rw [ih]
      ring

lemma codes_weights (t : HTree) : (((codes t).map Prod.fst : List ℝ) : Multiset ℝ) = weights t := by
  induction t with
  | leaf w => simp [codes]
  | node l r ihl ihr =>
      simp only [codes, List.map_append, List.map_map, Function.comp_def, weights_node]
      rw [← ihl, ← ihr]
      simp

lemma codes_weight_sum (t : HTree) : ((codes t).map Prod.fst).sum = wt t := by
  have h := codes_weights t
  have : (((codes t).map Prod.fst : List ℝ) : Multiset ℝ).sum = (weights t).sum := by rw [h]
  simpa [wt_eq_sum_weights] using this

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

lemma codes_ne_nil (t : HTree) : codes t ≠ [] := by
  induction t with
  | leaf w => simp [codes]
  | node l r ihl ihr => simp [codes, ihl]

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
def PFW (L : List (ℝ × List Bool)) : Prop :=
  L.Pairwise (fun p q => ¬ p.2.IsPrefix q.2 ∧ ¬ q.2.IsPrefix p.2)

lemma pfw_iff (L : List (ℝ × List Bool)) : PFW L ↔ IsPrefixCode (L.map Prod.snd) := by
  simp [PFW, IsPrefixCode, List.pairwise_map]

/-- The codewords beginning with the bit `b`, with that bit stripped. -/
def branch (b : Bool) (L : List (ℝ × List Bool)) : List (ℝ × List Bool) :=
  L.filterMap (fun p => match p.2 with
    | [] => none
    | d :: c => if d = b then some (p.1, c) else none)

@[simp] lemma branch_nil (b : Bool) : branch b [] = [] := rfl

@[simp] lemma branch_cons_nil (b : Bool) (w : ℝ) (L : List (ℝ × List Bool)) :
    branch b ((w, []) :: L) = branch b L := rfl

lemma branch_cons (b d : Bool) (w : ℝ) (c : List Bool) (L : List (ℝ × List Bool)) :
    branch b ((w, d :: c) :: L) = if d = b then (w, c) :: branch b L else branch b L := by
  by_cases h : d = b <;> simp [branch, h]

lemma branch_mem {b : Bool} {L : List (ℝ × List Bool)} {p : ℝ × List Bool}
    (hp : p ∈ branch b L) : (p.1, b :: p.2) ∈ L := by
  induction L with
  | nil => simp at hp
  | cons q L ih =>
      obtain ⟨w, c⟩ := q
      cases c with
      | nil => exact List.mem_cons_of_mem _ (ih (by simpa using hp))
      | cons d c =>
          rw [branch_cons] at hp
          by_cases hd : d = b
          · subst hd
            rw [if_pos rfl] at hp
            rcases List.mem_cons.1 hp with h1 | h1
            · rw [h1]; simp
            · exact List.mem_cons_of_mem _ (ih h1)
          · rw [if_neg hd] at hp
            exact List.mem_cons_of_mem _ (ih hp)

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

lemma branch_cost : ∀ L : List (ℝ × List Bool), (∀ p ∈ L, p.2 ≠ []) →
    codeCost (branch false L) + codeCost (branch true L) + (L.map Prod.fst).sum
      = codeCost L := by
  intro L
  induction L with
  | nil => simp [codeCost]
  | cons p L ih =>
      intro h
      obtain ⟨w, c⟩ := p
      cases c with
      | nil => exact absurd rfl (h (w, []) (by simp))
      | cons d c =>
          have ih' := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
          cases d
          · rw [branch_cons, branch_cons, if_pos rfl, if_neg (by simp)]
            simp only [codeCost, List.map_cons, List.sum_cons, List.length_cons] at *
            push_cast
            linarith
          · rw [branch_cons, branch_cons, if_neg (by simp), if_pos rfl]
            simp only [codeCost, List.map_cons, List.sum_cons, List.length_cons] at *
            push_cast
            linarith

lemma branch_len : ∀ L : List (ℝ × List Bool), (∀ p ∈ L, p.2 ≠ []) →
    ((branch false L).map (fun p => p.2.length)).sum
      + ((branch true L).map (fun p => p.2.length)).sum + L.length
      = (L.map (fun p => p.2.length)).sum := by
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
            simp only [List.map_cons, List.sum_cons, List.length_cons] at *
            omega
          · rw [branch_cons, branch_cons, if_neg (by simp), if_pos rfl]
            simp only [List.map_cons, List.sum_cons, List.length_cons] at *
            omega

/-- Every prefix code with nonnegative weights is realised, at no greater expected
codeword length, by a binary code tree with the same multiset of weights. -/
lemma exists_tree_of_prefixCode (n : ℕ) : ∀ L : List (ℝ × List Bool),
    (L.map (fun p => p.2.length)).sum ≤ n → L ≠ [] → (∀ p ∈ L, 0 ≤ p.1) → PFW L →
    ∃ t : HTree, weights t = ((L.map Prod.fst : List ℝ) : Multiset ℝ) ∧ cost t ≤ codeCost L := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro L hlen hne hpos hpf
    match L, hne with
    | [(w, c)], _ =>
        refine ⟨leaf w, by simp, ?_⟩
        have hw : 0 ≤ w := hpos (w, c) (by simp)
        have : (0 : ℝ) ≤ w * (c.length : ℝ) := by positivity
        simpa [codeCost] using this
    | (w1, c1) :: (w2, c2) :: rest, _ =>
        set L : List (ℝ × List Bool) := (w1, c1) :: (w2, c2) :: rest with hL
        have hpf2 := hpf
        rw [PFW, List.pairwise_cons] at hpf2
        obtain ⟨h1, hpf3⟩ := hpf2
        have hc1 : c1 ≠ [] := by
          intro hcon
          have := (h1 (w2, c2) (by simp)).1
          rw [hcon] at this
          exact this (List.nil_prefix)
        have hcne : ∀ p ∈ L, p.2 ≠ [] := by
          intro p hp
          rcases List.mem_cons.1 hp with h | h
          · rw [h]; exact hc1
          · intro hcon
            have := (h1 p h).2
            rw [hcon] at this
            exact this (List.nil_prefix)
        have hlenb := branch_len L hcne
        have hLlen : 2 ≤ L.length := by simp [hL]
        have hb0len : ((branch false L).map (fun p => p.2.length)).sum ≤ n - 2 := by omega
        have hb1len : ((branch true L).map (fun p => p.2.length)).sum ≤ n - 2 := by omega
        have hn2 : n - 2 < n := by
          have : 2 ≤ (L.map (fun p => p.2.length)).sum := by omega
          omega
        have hposb : ∀ b : Bool, ∀ p ∈ branch b L, 0 ≤ p.1 := by
          intro b p hp
          exact hpos (p.1, b :: p.2) (branch_mem hp)
        have hwsum := branch_weights L hcne
        have hcsum := branch_cost L hcne
        have hsum0 : (0 : ℝ) ≤ (L.map Prod.fst).sum := by
          apply List.sum_nonneg
          intro x hx
          simp only [List.mem_map] at hx
          obtain ⟨p, hp, rfl⟩ := hx
          exact hpos p hp
        by_cases h0 : branch false L = []
        · have h1' : branch true L ≠ [] := by
            intro hcon
            have : (((L.map Prod.fst : List ℝ) : Multiset ℝ)) = 0 := by
              rw [← hwsum, h0, hcon]; simp
            rw [hL] at this
            simp at this
          obtain ⟨t, htw, htc⟩ := ih (n - 2) hn2 (branch true L) hb1len h1' (hposb true)
            (branch_pfw true L hpf)
          refine ⟨t, ?_, ?_⟩
          · rw [htw, ← hwsum, h0]; simp
          · rw [h0, codeCost_nil] at hcsum
            linarith
        · by_cases h1'' : branch true L = []
          · obtain ⟨t, htw, htc⟩ := ih (n - 2) hn2 (branch false L) hb0len h0 (hposb false)
              (branch_pfw false L hpf)
            refine ⟨t, ?_, ?_⟩
            · rw [htw, ← hwsum, h1'']; simp
            · rw [h1'', codeCost_nil] at hcsum
              linarith
          · obtain ⟨t0, ht0w, ht0c⟩ := ih (n - 2) hn2 (branch false L) hb0len h0 (hposb false)
              (branch_pfw false L hpf)
            obtain ⟨t1, ht1w, ht1c⟩ := ih (n - 2) hn2 (branch true L) hb1len h1'' (hposb true)
              (branch_pfw true L hpf)
            refine ⟨node t0 t1, by rw [weights_node, ht0w, ht1w, hwsum], ?_⟩
            have hwt0 : wt t0 = ((branch false L).map Prod.fst).sum := by
              rw [wt_eq_sum_weights, ht0w]; simp
            have hwt1 : wt t1 = ((branch true L).map Prod.fst).sum := by
              rw [wt_eq_sum_weights, ht1w]; simp
            have hsplit : ((branch false L).map Prod.fst).sum
                + ((branch true L).map Prod.fst).sum = (L.map Prod.fst).sum := by
              have := congrArg Multiset.sum hwsum
              simpa using this
            rw [cost_node, hwt0, hwt1]
            linarith

/-- Optimality of the Huffman tree among all binary code trees with the same leaf weights. -/
theorem huffman_optimal_tree (ws : List ℝ) (hne : ws ≠ []) :
    weights (huffman ws) = (ws : Multiset ℝ) ∧
      ∀ t : HTree, weights t = (ws : Multiset ℝ) → cost (huffman ws) ≤ cost t := by
  have hperm : (List.insertionSort (· ≤ ·) ws).Perm ws := List.perm_insertionSort _ _
  have hcoe : ((List.insertionSort (· ≤ ·) ws : List ℝ) : Multiset ℝ) = (ws : Multiset ℝ) :=
    Multiset.coe_eq_coe.2 hperm
  have hsne : (List.insertionSort (· ≤ ·) ws) ≠ [] := by
    intro hcon
    apply hne
    have hlen := hperm.length_eq
    rw [hcon] at hlen
    exact List.eq_nil_of_length_eq_zero hlen.symm
  have hmne : ((List.insertionSort (· ≤ ·) ws).map HTree.leaf) ≠ [] := by
    simpa using hsne
  refine ⟨?_, ?_⟩
  · rw [huffman, huffTree_leaves _ hmne, sum_weights_leaves, hcoe]
  · intro t ht
    rw [huffman, huffTree_cost _ hmne, sum_cost_leaves, map_wt_leaves, zero_add]
    exact hcost_le _ (List.pairwise_insertionSort _ _) t (by rw [ht, ← hcoe])

/-- **Huffman coding is optimal: it minimizes the expected codeword length among all
binary prefix codes.**

Given a nonempty list `ws` of nonnegative symbol weights (e.g. probabilities), the
Huffman code `codes (huffman ws)` assigns a binary codeword to each symbol so that

* the multiset of weights it encodes is exactly `ws`;
* it is a prefix code (no codeword is a prefix of another);
* its expected codeword length `∑ weight * (length of codeword)` is less than or equal to
  that of *every* prefix code for the same multiset of weights. -/
theorem huffman_optimal (ws : List ℝ) (hne : ws ≠ []) (hw : ∀ w ∈ ws, 0 ≤ w) :
    (((codes (huffman ws)).map Prod.fst : List ℝ) : Multiset ℝ) = (ws : Multiset ℝ) ∧
    IsPrefixCode ((codes (huffman ws)).map Prod.snd) ∧
    ∀ code : List (ℝ × List Bool),
      ((code.map Prod.fst : List ℝ) : Multiset ℝ) = (ws : Multiset ℝ) →
      IsPrefixCode (code.map Prod.snd) →
      codeCost (codes (huffman ws)) ≤ codeCost code := by
  obtain ⟨hwe, hopt⟩ := huffman_optimal_tree ws hne
  refine ⟨by rw [codes_weights, hwe], codes_isPrefixCode _, ?_⟩
  intro code hcw hcp
  have hcne : code ≠ [] := by
    intro hcon
    apply hne
    rw [hcon] at hcw
    simp only [List.map_nil, Multiset.coe_nil] at hcw
    exact (Multiset.coe_eq_zero ws).1 hcw.symm
  have hcpos : ∀ p ∈ code, 0 ≤ p.1 := by
    intro p hp
    have : p.1 ∈ ((code.map Prod.fst : List ℝ) : Multiset ℝ) := by
      simp only [Multiset.mem_coe, List.mem_map]
      exact ⟨p, hp, rfl⟩
    rw [hcw] at this
    exact hw p.1 (Multiset.mem_coe.1 this)
  obtain ⟨t, htw, htc⟩ := exists_tree_of_prefixCode
    ((code.map (fun p => p.2.length)).sum) code le_rfl hcne hcpos ((pfw_iff code).2 hcp)
  calc codeCost (codes (huffman ws)) = cost (huffman ws) := codes_cost _
    _ ≤ cost t := hopt t (by rw [htw, hcw])
    _ ≤ codeCost code := htc

/-- Sanity check: for two symbols of equal weight the Huffman code assigns one bit to
each, for a total expected length of `2`. -/
example : codeCost (codes (huffman [1, 1])) = 2 := by
  norm_num [huffman, List.insertionSort, List.orderedInsert, huffTree, codes, codeCost]

/-- Sanity check: weights `1, 2, 3` give codeword lengths `2, 2, 1`, i.e. expected
length `1*2 + 2*2 + 3*1 = 9`. -/
example : codeCost (codes (huffman [1, 2, 3])) = 9 := by
  norm_num [huffman, List.insertionSort, List.orderedInsert, huffTree, codes, codeCost, wt]

end CS

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

