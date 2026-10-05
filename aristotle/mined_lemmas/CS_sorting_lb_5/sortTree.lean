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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace CS

/-- A comparison-based decision tree sorting 5 elements: an internal node
`node i j l r` compares the keys at positions `i` and `j`, descending into `l`
when `a i ≤ a j` and into `r` otherwise; a leaf outputs a permutation of the
positions. -/
inductive CompTree where
  | leaf : Equiv.Perm (Fin 5) → CompTree
  | node : Fin 5 → Fin 5 → CompTree → CompTree → CompTree
  deriving Inhabited

namespace CompTree

/-- The worst-case number of comparisons performed by the decision tree. -/

noncomputable def sortTree : CompTree :=
  build (Finset.univ : Finset (Fin 5 × Fin 5)).toList (fun _ _ => true)

