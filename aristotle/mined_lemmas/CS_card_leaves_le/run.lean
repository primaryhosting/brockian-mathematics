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

def run : CompTree n → Equiv.Perm (Fin n) → Equiv.Perm (Fin n)
  | .leaf p, _ => p
  | .node i j l r, σ => if σ i < σ j then l.run σ else r.run σ

/-- The finite set of outputs occurring at the leaves of the tree. -/
