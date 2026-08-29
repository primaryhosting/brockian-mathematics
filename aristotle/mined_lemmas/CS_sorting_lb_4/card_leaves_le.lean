import Mathlib

/-!
# Sorting Lb 4
Category: Computer Science
Target: CS.sorting_lb_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

/-- A comparison-based decision tree for sorting four elements.
Each internal node compares two positions `i j` of the input; the algorithm
branches on the answer.  Each leaf outputs a permutation (the claimed sorted
order of the input). -/
inductive CompTree : Type
  | leaf (out : Equiv.Perm (Fin 4)) : CompTree
  | node (i j : Fin 4) (l r : CompTree) : CompTree
  deriving Inhabited

namespace CompTree

/-- The worst-case number of comparisons performed by the tree. -/

theorem card_leaves_le (t : CompTree) : t.leaves.card ≤ 2 ^ t.depth := by
  induction t with
  | leaf o => simp [leaves, depth]
  | node i j l r ihl ihr =>
      refine le_trans (Finset.card_union_le _ _) ?_
      have hl : l.leaves.card ≤ 2 ^ (max l.depth r.depth) :=
        ihl.trans (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _))
      have hr : r.leaves.card ≤ 2 ^ (max l.depth r.depth) :=
        ihr.trans (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _))
      calc l.leaves.card + r.leaves.card
          ≤ 2 ^ (max l.depth r.depth) + 2 ^ (max l.depth r.depth) := add_le_add hl hr
        _ = 2 ^ (depth (node i j l r)) := by simp [depth, pow_succ]; ring

/-- A tree *sorts correctly* if, on every input ranking `p`, it outputs `p`
(equivalently, it determines the correct ordering of the four elements). -/
