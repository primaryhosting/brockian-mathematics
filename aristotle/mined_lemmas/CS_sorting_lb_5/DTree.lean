import Mathlib

/-!
# Sorting Lb 5
Category: Computer Science
Target: CS.sorting_lb_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

/-- An input to a comparison sort of 5 elements is a "ranking": a permutation `s` of `Fin 5`
assigning to each position `i` its rank `s i`.  A comparison of positions `i` and `j` returns
`decide (s i < s j)`. -/
abbrev Rank := Equiv.Perm (Fin 5)

/-- A comparison-based decision tree for sorting 5 elements: an internal node compares two
positions and branches on the outcome, a leaf outputs a permutation (the claimed ranking). -/
inductive DTree : Type
  | leaf : Rank → DTree
  | node : Fin 5 → Fin 5 → DTree → DTree → DTree

/-- The worst-case number of comparisons performed by the tree. -/

lemma DTree.card_image_run_le (t : DTree) :
    (Finset.univ.image t.run).card ≤ 2 ^ t.depth := by
  induction t with
  | leaf p =>
      have : (Finset.univ.image (DTree.leaf p).run) = {p} := by
        ext x
        simp [DTree.run, eq_comm]
      simp [this, DTree.depth]
  | node i j l r ihl ihr =>
      have hsub : Finset.univ.image (DTree.node i j l r).run ⊆
          (Finset.univ.image l.run) ∪ (Finset.univ.image r.run) := by
        intro x hx
        simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
        obtain ⟨s, hs⟩ := hx
        simp only [DTree.run] at hs
        by_cases h : s i < s j
        · rw [if_pos h] at hs
          exact Finset.mem_union_left _ (Finset.mem_image.2 ⟨s, Finset.mem_univ _, hs⟩)
        · rw [if_neg h] at hs
          exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨s, Finset.mem_univ _, hs⟩)
      calc (Finset.univ.image (DTree.node i j l r).run).card
          ≤ ((Finset.univ.image l.run) ∪ (Finset.univ.image r.run)).card :=
            Finset.card_le_card hsub
        _ ≤ (Finset.univ.image l.run).card + (Finset.univ.image r.run).card :=
            Finset.card_union_le _ _
        _ ≤ 2 ^ l.depth + 2 ^ r.depth := Nat.add_le_add ihl ihr
        _ ≤ 2 ^ (DTree.node i j l r).depth := by
            have h1 : (2:ℕ) ^ l.depth ≤ 2 ^ (max l.depth r.depth) :=
              Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
            have h2 : (2:ℕ) ^ r.depth ≤ 2 ^ (max l.depth r.depth) :=
              Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
            simp only [DTree.depth, pow_succ]
            omega

/-- **Comparison-sort lower bound for 5 elements.**
Any comparison-based decision tree that correctly sorts every arrangement of 5 elements
(i.e. outputs the true ranking on every input) makes at least `⌈log₂ (5!)⌉ = 7` comparisons
in the worst case. -/
