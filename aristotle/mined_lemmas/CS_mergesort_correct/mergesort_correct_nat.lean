/-!
# Mergesort Correct
Category: Computer Science
Target: CS.mergesort_correct
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

universe u

variable {α : Type u}

/-- Split a list into two lists by alternately distributing its elements. -/

theorem mergesort_correct_nat (l : List Nat) :
    List.Pairwise (fun a b => a ≤ b) (mergesort (fun a b => decide (a ≤ b)) l) ∧
      (mergesort (fun a b => decide (a ≤ b)) l).Perm l := by
  have h := mergesort_correct (fun a b => decide (a ≤ b))
    (by intro a b c hab hbc; simp only [decide_eq_true_eq] at *; omega)
    (by intro a b; by_cases h : a ≤ b <;> simp [h] <;> omega) l
  refine ⟨?_, h.2⟩
  have := h.1
  simpa using this

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

