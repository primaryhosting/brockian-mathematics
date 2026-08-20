/-
# Sorting Lb 5
Category: Computer Science
Target: CS.sorting_lb_5
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
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace CS

/-- A comparison-based sorting algorithm on `n` elements, modelled as a binary
decision tree.  A `leaf p` reports that the input order is described by the
permutation `p`; a `node i j l r` compares the `i`-th and `j`-th input entries
and continues in the left subtree if `aᵢ < a_j`, in the right subtree otherwise. -/
inductive DTree (n : ℕ) : Type
  | leaf : Equiv.Perm (Fin n) → DTree n
  | node : Fin n → Fin n → DTree n → DTree n → DTree n

namespace DTree

variable {n : ℕ}

/-- The number of comparisons performed in the worst case, i.e. the height of the tree. -/

def Correct (t : DTree n) : Prop := ∀ σ : Equiv.Perm (Fin n), t.run σ = σ

/-- A correct comparison sort must be able to output all `n!` permutations, hence
`n ! ≤ 2 ^ depth`. -/
