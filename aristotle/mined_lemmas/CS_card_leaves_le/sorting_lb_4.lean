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

theorem sorting_lb_4 (t : CompTree 4) (h : t.Sorts) : Nat.clog 2 (4 !) ≤ t.depth := by
  have hcard : (4 ! : ℕ) ≤ 2 ^ t.depth :=
    (CompTree.factorial_le_card_leaves t h).trans (CompTree.card_leaves_le t)
  exact Nat.clog_le_of_le_pow hcard

/-- The bound of `sorting_lb_4` is the number `5`. -/
