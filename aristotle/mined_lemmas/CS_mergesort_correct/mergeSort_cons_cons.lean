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

/-!
# Mergesort Correct
Category: Computer Science
Target: CS.mergesort_correct
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

universe u

variable {α : Type u} (r : α → α → Prop) [DecidableRel r]

/-- Merge two lists with respect to a decidable relation `r`.
The smaller head (according to `r`) is emitted first. -/

theorem mergeSort_cons_cons (a b : α) (t : List α) :
    mergeSort r (a :: b :: t) =
      merge r (mergeSort r ((a :: b :: t).take ((a :: b :: t).length / 2)))
        (mergeSort r ((a :: b :: t).drop ((a :: b :: t).length / 2))) := by
  rw [mergeSort]

/-! ### Correctness of `merge` -/

/-- `merge r xs ys` is a permutation of `xs ++ ys`. -/
