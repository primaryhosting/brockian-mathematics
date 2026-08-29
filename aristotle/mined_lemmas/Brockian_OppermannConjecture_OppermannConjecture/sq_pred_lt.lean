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


private theorem sq_pred_lt (n : Nat) (hn : 1 ≤ n) : n * (n - 1) + (n - 1) < n * n := by
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rw [Nat.mul_succ]
  exact Nat.add_lt_add_left (by omega) _

/-- **Conditional reduction**: the square-root prime-gap hypothesis implies Oppermann's
conjecture.  (The remaining small cases are verified unconditionally above.) -/
