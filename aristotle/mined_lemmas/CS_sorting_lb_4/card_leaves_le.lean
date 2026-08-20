/-
# Sorting Lb 4
Category: Computer Science
Target: CS.sorting_lb_4
Verification: verified (axiom-clean: propext, Classical.choice, Quot.sound)
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace CS

/-- A comparison-based decision tree sorting 4 elements.  A `leaf` outputs a
permutation (the claimed sorted order / ranking of the input), and a `node i j`
compares the input keys at positions `i` and `j` and branches accordingly. -/
inductive DTree where
  | leaf : Equiv.Perm (Fin 4) → DTree
  | node : Fin 4 → Fin 4 → DTree → DTree → DTree
  deriving Inhabited

namespace DTree

/-- The worst-case number of comparisons performed by the tree. -/

theorem card_leaves_le (t : DTree) : (leaves t).card ≤ 2 ^ depth t := by
  induction t with
  | leaf p => simp [leaves, depth]
  | node i j t f iht ihf =>
      refine le_trans (Finset.card_union_le _ _) ?_
      have h1 : (leaves t).card ≤ 2 ^ (max (depth t) (depth f)) :=
        iht.trans (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _))
      have h2 : (leaves f).card ≤ 2 ^ (max (depth t) (depth f)) :=
        ihf.trans (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _))
      calc (leaves t).card + (leaves f).card
          ≤ 2 ^ (max (depth t) (depth f)) + 2 ^ (max (depth t) (depth f)) :=
            Nat.add_le_add h1 h2
        _ = 2 ^ depth (node i j t f) := by simp [depth, pow_succ]; ring

end DTree

/-- **Comparison-sort lower bound for 4 elements.**
Any correct comparison-based sorting decision tree for 4 elements must have
worst-case depth at least `⌈log₂ 4!⌉ = 5`. -/
