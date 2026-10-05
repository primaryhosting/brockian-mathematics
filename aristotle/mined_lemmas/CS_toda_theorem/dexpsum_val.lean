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

/-
Gap functions (differences of witness counts) and their closure properties.
-/
import RequestProject.Toda.Framework

namespace CS

open scoped BigOperators

/-! ### Splitting witnesses -/


theorem dexpsum_val (v : ℕ) (d : GapData) (n : ℕ) (x : Assign) :
    (dexpsum v d).val n x = ∑ z : Fin v → Bool, d.val (n + v) (ext n v x z) := by
  show ∑ y : Fin (v + d.w) → Bool, d.wt (ext n (v + d.w) x y) = _
  rw [sum_split v d.w]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [val]
  refine Finset.sum_congr rfl fun y2 _ => ?_
  rw [ext_append]

