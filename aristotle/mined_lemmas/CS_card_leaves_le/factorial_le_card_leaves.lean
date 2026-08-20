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

theorem factorial_le_card_leaves (t : CompTree n) (h : t.Sorts) :
    n ! ≤ t.leaves.card := by
  have huniv : (Finset.univ : Finset (Equiv.Perm (Fin n))) ⊆ t.leaves := by
    intro σ _
    have := run_mem_leaves t σ
    rwa [h σ] at this
  have := Finset.card_le_card huniv
  simpa [Fintype.card_perm] using this

end CompTree

/-- **Comparison-sort lower bound for 4 elements.**
Any correct comparison sort of 4 elements needs at least `⌈log₂ (4!)⌉ = 5` comparisons
in the worst case. -/
