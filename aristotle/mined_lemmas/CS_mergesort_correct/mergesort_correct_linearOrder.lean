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

variable {α : Type*}

/-- Merge two lists with respect to a boolean comparison `le`. -/

theorem mergesort_correct_linearOrder [LinearOrder α] (l : List α) :
    List.Pairwise (· ≤ ·) (msort (fun a b => decide (a ≤ b)) l) ∧
      (msort (fun a b => decide (a ≤ b)) l).Perm l := by
  refine ⟨?_, msort_perm _ l⟩
  have := msort_pairwise (α := α) (fun a b => decide (a ≤ b))
    (by intro a b c hab hbc; simp only [decide_eq_true_eq] at *; exact le_trans hab hbc)
    (by intro a b; simp only [decide_eq_true_eq]; exact le_total a b) l
  simpa using this

end CS

