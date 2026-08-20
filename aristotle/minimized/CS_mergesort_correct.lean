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

import Mathlib
import RequestProject.Mergesort

/-!
# Mergesort Correct — specializations

Specializations of `CS.mergesort_correct` to a decidable total transitive relation,
and in particular to `(· ≤ ·)` on `ℕ`.
-/

namespace CS

/-- Mergesort correctness for a decidable total transitive relation `r`. -/

theorem mergesort_correct_rel {α : Type*} (r : α → α → Prop) [DecidableRel r] [Std.Total r]
    [IsTrans α r] (l : List α) :
    List.Pairwise r (l.mergeSort fun a b => decide (r a b)) ∧
      (l.mergeSort fun a b => decide (r a b)).Perm l :=
  ⟨List.pairwise_mergeSort' r l, List.mergeSort_perm l _⟩

/-- Mergesort correctness on `ℕ` with the usual order. -/
