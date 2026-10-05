/-
# Insertion Sort Correct
Category: Computer Science
Target: CS.insertion_sort_correct
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace CS

/--
**Insertion sort is correct.**

For any relation `r` that is total and transitive (so that `List.Pairwise r` is the
expected notion of sortedness), `List.insertionSort r l` is pairwise-sorted with respect to
`r` and is a permutation of the input list `l`.

The two components are closed by Mathlib's `List.pairwise_insertionSort`
(sortedness) and `List.perm_insertionSort` (permutation).
-/

theorem insertion_sort_correct_linearOrder {α : Type*} [LinearOrder α] (l : List α) :
    (List.insertionSort (· ≤ ·) l).Pairwise (· ≤ ·) ∧
      (List.insertionSort (· ≤ ·) l).Perm l :=
  insertion_sort_correct _ l

end CS

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

