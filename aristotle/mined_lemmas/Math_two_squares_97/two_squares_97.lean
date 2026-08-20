import Mathlib
import RequestProject.TwoSquares97

/-!
# Two Squares 97, phrased with Mathlib's `Nat.Prime`

This file restates `Math.two_squares_97` using `Nat.Prime`.
-/

namespace Math

/-- The prime `97` is a sum of two squares: `97 = 4 ^ 2 + 9 ^ 2`. -/

theorem two_squares_97 :
    (2 ≤ 97 ∧ ∀ m : Nat, m ∣ 97 → m = 1 ∨ m = 97) ∧ ∃ a b : Nat, 97 = a ^ 2 + b ^ 2 := by
  refine ⟨⟨by omega, ?_⟩, 4, 9, by decide⟩
  have h : ∀ m < 98, m ∣ 97 → m = 1 ∨ m = 97 := by decide
  intro m hm
  exact h m (Nat.lt_succ_of_le (Nat.le_of_dvd (by omega) hm)) hm

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

