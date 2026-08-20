/-
# Sorting Lb 3
Category: Computer Science
Target: CS.sorting_lb_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Sorting Lb 3
Category: Computer Science
Target: CS.sorting_lb_3
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace CS

/-- An *input* to a comparison sort of three elements is described by the permutation
`σ : Equiv.Perm (Fin 3)` sending each position `i` to the rank of the element stored there. -/
abbrev Input : Type := Equiv.Perm (Fin 3)

/-- The outcome of comparing the elements stored at positions `i` and `j`
of the input described by `σ`: `true` means "the element at `i` is at most the one at `j`". -/

def cost : DTree → Input → ℕ
  | .leaf _, _ => 0
  | .node i j l r, σ => 1 + (if ans σ i j then cost l σ else cost r σ)

/-- Counting bound: if an algorithm distinguishes all the inputs of a set `S`
(i.e. gives them pairwise different outputs) using at most `d` comparisons on each of them,
then `S` has at most `2 ^ d` elements. -/
