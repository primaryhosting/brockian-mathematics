import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace CS

/-- A comparison-based decision tree for sorting 3 elements.

An input is a permutation `s : Equiv.Perm (Fin 3)`, thought of as assigning to each
position `i` its rank `s i`.  An internal node `node i j l r` compares the keys at
positions `i` and `j`, descending into `l` if `s i < s j` and into `r` otherwise.
A leaf outputs a permutation, the algorithm's claimed ranking of the input. -/
inductive DTree where
  | leaf : Equiv.Perm (Fin 3) → DTree
  | node : Fin 3 → Fin 3 → DTree → DTree → DTree

namespace DTree

/-- The worst-case number of comparisons performed by the tree, i.e. its height. -/

lemma length_leaves_le (t : DTree) : t.leaves.length ≤ 2 ^ t.depth := by
  induction t with
  | leaf p => simp [leaves, depth]
  | node i j l r ihl ihr =>
      have h1 : l.leaves.length ≤ 2 ^ (max l.depth r.depth) :=
        ihl.trans (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _))
      have h2 : r.leaves.length ≤ 2 ^ (max l.depth r.depth) :=
        ihr.trans (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _))
      have : l.leaves.length + r.leaves.length ≤ 2 ^ (max l.depth r.depth) +
          2 ^ (max l.depth r.depth) := Nat.add_le_add h1 h2
      have hp : 2 ^ (1 + max l.depth r.depth)
          = 2 ^ (max l.depth r.depth) + 2 ^ (max l.depth r.depth) := by
        rw [pow_add, pow_one]; ring
      simpa [leaves, depth, hp] using this

end DTree

/-- A decision tree *sorts* if on every input ranking it outputs that ranking. -/
