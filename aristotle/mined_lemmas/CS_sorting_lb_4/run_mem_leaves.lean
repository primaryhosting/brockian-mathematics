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

theorem run_mem_leaves (t : DTree n) (σ : Equiv.Perm (Fin n)) : run t σ ∈ leaves t := by
  induction t with
  | leaf p => simp [run, leaves]
  | node i j a b ha hb =>
      by_cases h : σ i ≤ σ j <;> simp [run, leaves, h, ha, hb]

