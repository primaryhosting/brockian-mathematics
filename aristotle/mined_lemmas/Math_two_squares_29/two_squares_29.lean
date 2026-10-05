import Mathlib
import RequestProject.TwoSquares29

/-!
# Two Squares 29 (Mathlib restatement)

A restatement of `Math.two_squares_29` using Mathlib's `Nat.Prime`.
-/

namespace Math

/-- The prime `29` is a sum of two squares: `29 = 2 ^ 2 + 5 ^ 2`. -/

theorem two_squares_29 :
    (1 < 29 ∧ ∀ m : Nat, m ∣ 29 → m = 1 ∨ m = 29) ∧ ∃ a b : Nat, 29 = a ^ 2 + b ^ 2 := by
  refine ⟨⟨by decide, ?_⟩, 2, 5, by decide⟩
  have key : ∀ m < 30, m ∣ 29 → m = 1 ∨ m = 29 := by decide
  intro m hm
  exact key m (Nat.lt_succ_of_le (Nat.le_of_dvd (by decide) hm)) hm

end Math

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

