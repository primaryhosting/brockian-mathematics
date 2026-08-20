/-
# Sorting Lb 4
Category: Computer Science
Target: CS.sorting_lb_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Sorting Lb 4

Any comparison sort of `4` elements needs at least `⌈log₂(4!)⌉ = 5` comparisons in the
worst case.

A comparison sort is modelled as a (binary) decision tree: an internal node compares two
input positions `i` and `j`, and branches on the answer; a leaf outputs a permutation
(the claimed sorted order).  An input is a permutation `σ` assigning to each position its
rank, and the comparison `i ≤ j` is answered by `σ i ≤ σ j`.  The tree *sorts* if on every
input it outputs the correct permutation.

The main result `CS.sorting_lb_4` states that any such tree for `4` elements has depth at
least `Nat.clog 2 (4!) = 5`.
-/

namespace CS

/-- A comparison-based decision tree on `n` elements: a leaf carries the output
permutation, an internal node compares positions `i` and `j`. -/
inductive DTree (n : ℕ) where
  | leaf : Equiv.Perm (Fin n) → DTree n
  | node : Fin n → Fin n → DTree n → DTree n → DTree n
  deriving Inhabited

namespace DTree

variable {n : ℕ}

/-- Worst-case number of comparisons performed by the tree. -/

theorem length_leaves_le (t : DTree n) : (leaves t).length ≤ 2 ^ depth t := by
  induction t with
  | leaf p => simp [leaves, depth]
  | node i j a b ha hb =>
      have h1 : (leaves a).length ≤ 2 ^ max (depth a) (depth b) :=
        ha.trans (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _))
      have h2 : (leaves b).length ≤ 2 ^ max (depth a) (depth b) :=
        hb.trans (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _))
      simp only [leaves, depth, List.length_append, pow_succ]
      omega

end DTree

open DTree

/-- Sanity check: the model is not vacuous.  For two elements, one comparison sorts. -/
example : ∀ σ : Equiv.Perm (Fin 2),
    run (DTree.node 0 1 (DTree.leaf 1) (DTree.leaf (Equiv.swap 0 1))) σ = σ := by decide

/-- A sorting tree must have at least `n !` leaves. -/
