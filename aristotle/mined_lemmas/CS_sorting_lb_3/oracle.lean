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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace CS

/-! # Information-theoretic lower bound for comparison sorting of 3 elements

We model a comparison-based sorting algorithm on `n` elements as a binary decision tree.
An internal node is a comparison query of two input positions `(i, j)`, whose two subtrees
are followed according to the (boolean) answer; a leaf is labelled with the answer the
algorithm outputs (the permutation that sorts the input).

The worst-case number of comparisons performed by the algorithm is the depth of the tree.

For `n = 3` we prove that any correct comparison sort has depth at least
`⌈log₂ (3!)⌉ = Nat.clog 2 (3!) = 3`.
-/

/-- A comparison decision tree on `n` positions with answers in `α`:
either a leaf carrying an output, or a comparison of two positions with the
two continuation subtrees. -/
inductive DTree (n : ℕ) (α : Type*) where
  | leaf : α → DTree n α
  | node : Fin n → Fin n → DTree n α → DTree n α → DTree n α
  deriving Inhabited

namespace DTree

variable {n : ℕ} {α : Type*}

/-- The depth of a decision tree: the worst-case number of comparisons it performs. -/

def oracle {n : ℕ} (key : Fin n → ℕ) : Fin n → Fin n → Bool := fun i j => decide (key i ≤ key j)

/-- A decision tree `t` is a *correct comparison sort* on `n` elements if, for every input
whose relative order is described by the ranking `σ : Equiv.Perm (Fin n)` (position `i` holds
the element of rank `σ i`), running `t` on the comparison oracle of that input outputs `σ`,
i.e. the algorithm determines the ordering of the input. -/
