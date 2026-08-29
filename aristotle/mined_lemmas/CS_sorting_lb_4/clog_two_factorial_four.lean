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
Category: Computer Science
Target: CS.sorting_lb_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace CS

/-- A comparison-based sorting algorithm for `n` elements, modelled as a binary
decision tree.  An internal node `node i j l r` compares the inputs at positions
`i` and `j`, descending into `l` if `a i < a j` and into `r` otherwise; a leaf
`leaf p` outputs the permutation `p`. -/
inductive CompTree (n : ℕ) : Type
  | leaf : Equiv.Perm (Fin n) → CompTree n
  | node : Fin n → Fin n → CompTree n → CompTree n → CompTree n
  deriving Inhabited

namespace CompTree

variable {n : ℕ}

/-- The worst-case number of comparisons performed by the algorithm, i.e. the
height of the decision tree. -/

theorem clog_two_factorial_four : Nat.clog 2 (Nat.factorial 4) = 5 := by
  norm_num [Nat.factorial]

/-- Restatement of `CS.sorting_lb_4`: at least 5 comparisons are needed. -/
