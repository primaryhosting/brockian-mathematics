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


theorem sum_split {M : Type*} [AddCommMonoid M] (w v : ℕ) (F : (Fin (w + v) → Bool) → M) :
    ∑ y : Fin (w + v) → Bool, F y
      = ∑ y1 : Fin w → Bool, ∑ y2 : Fin v → Bool, F (Fin.append y1 y2) := by
  have h := Equiv.sum_comp (Fin.appendEquiv w v) F
  rw [← h, Fintype.sum_prod_type]
  rfl

/-- The sub-witness of `y` of length `w` starting at position `k`. -/
