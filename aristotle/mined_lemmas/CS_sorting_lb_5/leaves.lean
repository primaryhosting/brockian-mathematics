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

/-- A comparison-sorting algorithm on `n` elements, modelled as a binary decision tree.

The hidden input is a permutation `σ : Equiv.Perm (Fin n)`, thought of as the ranking of the
`n` input elements: element `i` has rank `σ i`.  An internal node `node i j l r` compares
elements `i` and `j`; the algorithm continues in `l` if `σ i < σ j` and in `r` otherwise.
A leaf reports the permutation the algorithm has decided the input is. -/
inductive CTree (n : ℕ) : Type
  | leaf (p : Equiv.Perm (Fin n)) : CTree n
  | node (i j : Fin n) (l r : CTree n) : CTree n
  deriving Inhabited

namespace CTree

variable {n : ℕ}

/-- The output of the algorithm `t` on the input ranking `σ`. -/

def leaves : CTree n → List (Equiv.Perm (Fin n))
  | leaf p => [p]
  | node _ _ l r => l.leaves ++ r.leaves

/-- A binary tree of height `d` has at most `2 ^ d` leaves. -/
