/-
# Sorting Lb 3
Category: Computer Science
Target: CS.sorting_lb_3
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

/-- A comparison-based decision tree for sorting `3` elements.

An internal node `cmp i j l r` performs the comparison "is the element at position `i`
smaller than the element at position `j`?" and branches accordingly; a leaf reports the
permutation that the algorithm claims describes the input order. -/
inductive DTree3 : Type
  | leaf (out : Equiv.Perm (Fin 3)) : DTree3
  | cmp (i j : Fin 3) (l r : DTree3) : DTree3
  deriving Inhabited

namespace DTree3

/-- The worst-case number of comparisons performed by the decision tree, i.e. its depth. -/

theorem sorting_lb_3 (t : DTree3) (h : DTree3.Sorts t) :
    Nat.clog 2 (Nat.factorial 3) ≤ DTree3.depth t := by
  have hclog : Nat.clog 2 (Nat.factorial 3) = 3 := by decide
  rw [hclog]
  by_contra hlt
  push_neg at hlt
  have hd : DTree3.depth t ≤ 2 := by omega
  have h1 : (DTree3.outputs t).card ≤ 2 ^ DTree3.depth t := DTree3.card_outputs_le t
  have h2 : (2 : ℕ) ^ DTree3.depth t ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hd
  have h3 : 6 ≤ (DTree3.outputs t).card := DTree3.card_outputs_ge_of_sorts h
  omega


/-- The bound is tight and non-vacuous: there is a comparison-based decision tree of
depth exactly `3` that correctly sorts `3` elements. -/
