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

variable {α : Type u}

/-- Merge two lists with respect to a boolean comparison `le`. -/

theorem split_perm (l : List α) : ((split l).1 ++ (split l).2).Perm l := by
  induction l using split.induct with
  | case1 => simp [split]
  | case2 x => simp [split]
  | case3 x y t ih =>
      simp only [split, List.cons_append]
      refine List.Perm.trans (List.Perm.cons x ?_) (List.Perm.cons x (List.Perm.cons y ih))
      exact (List.perm_middle (a := y) (l₁ := (split t).1) (l₂ := (split t).2))

/-- Mergesort: split the list in two, sort the halves recursively, and merge them. -/
