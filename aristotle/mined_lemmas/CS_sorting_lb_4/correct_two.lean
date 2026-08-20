import Mathlib

/-!
# Sorting Lb 4
Category: Computer Science
Target: CS.sorting_lb_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace CS

/-- A comparison-based decision tree sorting `n` elements.
A `node (i, j) t f` compares the keys at positions `i` and `j`, descending into
`t` if the key at `i` is `≤` the key at `j`, and into `f` otherwise.
A `leaf p` outputs the permutation `p` describing the discovered order. -/
inductive DTree (n : ℕ) where
  | leaf : Equiv.Perm (Fin n) → DTree n
  | node : Fin n → Fin n → DTree n → DTree n → DTree n

namespace DTree

variable {n : ℕ}

/-- The worst-case number of comparisons performed by the tree. -/

theorem correct_two :
    Correct (node (n := 2) 0 1 (leaf 1) (leaf (Equiv.swap 0 1))) := by
  intro σ
  revert σ
  exact of_decide_eq_true (by rfl)

end DTree

/-- **Comparison-sort lower bound for 4 elements.**
Any correct comparison-based sorting algorithm on 4 elements, modelled as a
decision tree, performs at least `⌈log₂ (4!)⌉ = 5` comparisons in the worst case. -/
