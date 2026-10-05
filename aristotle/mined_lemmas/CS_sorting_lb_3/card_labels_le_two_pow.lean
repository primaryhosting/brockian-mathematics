import Mathlib

/-!
# Sorting Lb 3
Category: Computer Science
Target: CS.sorting_lb_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

/-- A comparison-based sorting algorithm for `3` elements, presented as a (binary)
decision tree.  An internal node `node i j l r` asks the comparison "is the `i`-th
input element smaller than the `j`-th one?" and branches accordingly; a leaf
`leaf p` outputs the permutation `p`. -/
inductive DTree : Type
  | leaf : Equiv.Perm (Fin 3) → DTree
  | node : Fin 3 → Fin 3 → DTree → DTree → DTree
  deriving Inhabited

namespace DTree

/-- Running the decision tree on the input whose ranking is the permutation `σ`
(i.e. the `i`-th input element has rank `σ i`): each comparison `i` vs `j`
is answered by the truth value of `σ i < σ j`. -/

theorem card_labels_le_two_pow (t : DTree) : (labels t).card ≤ 2 ^ depth t := by
  induction t with
  | leaf p => simp [labels, depth]
  | node i j l r ihl ihr =>
      refine le_trans (Finset.card_union_le _ _) ?_
      have hl : (labels l).card ≤ 2 ^ (max (depth l) (depth r)) :=
        ihl.trans (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _))
      have hr : (labels r).card ≤ 2 ^ (max (depth l) (depth r)) :=
        ihr.trans (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _))
      calc (labels l).card + (labels r).card
          ≤ 2 ^ (max (depth l) (depth r)) + 2 ^ (max (depth l) (depth r)) :=
            Nat.add_le_add hl hr
        _ = 2 ^ depth (node i j l r) := by rw [depth, pow_succ]; ring

/-- Every output of the tree is one of its leaf labels. -/
