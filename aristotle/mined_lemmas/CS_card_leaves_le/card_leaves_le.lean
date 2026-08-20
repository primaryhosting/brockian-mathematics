/-
# Sorting Lb 4
Category: Computer Science
Target: CS.sorting_lb_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace CS

/-- A comparison-based sorting algorithm on `n` elements, modelled as a binary decision tree.
A `node i j l r` compares the elements at positions `i` and `j`, continuing with `l` if the
`i`-th element is smaller and with `r` otherwise.  A `leaf p` outputs the permutation `p`. -/
inductive CompTree (n : ℕ) : Type where
  | leaf : Equiv.Perm (Fin n) → CompTree n
  | node : Fin n → Fin n → CompTree n → CompTree n → CompTree n

namespace CompTree

variable {n : ℕ}

/-- The worst-case number of comparisons performed, i.e. the depth of the decision tree. -/

theorem card_leaves_le (t : CompTree n) : t.leaves.card ≤ 2 ^ t.depth := by
  induction t with
  | leaf p => simp [leaves, depth]
  | node i j l r ihl ihr =>
      refine le_trans (Finset.card_union_le _ _) ?_
      have hl : l.leaves.card ≤ 2 ^ (max l.depth r.depth) :=
        ihl.trans (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _))
      have hr : r.leaves.card ≤ 2 ^ (max l.depth r.depth) :=
        ihr.trans (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _))
      calc l.leaves.card + r.leaves.card
          ≤ 2 ^ (max l.depth r.depth) + 2 ^ (max l.depth r.depth) := Nat.add_le_add hl hr
        _ = 2 ^ (max l.depth r.depth + 1) := by ring
  
/-- Every output of the algorithm occurs at some leaf. -/
