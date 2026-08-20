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
