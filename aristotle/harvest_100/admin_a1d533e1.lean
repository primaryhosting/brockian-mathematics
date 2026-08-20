/-
# Two Squares 89
Category: Pure Mathematics
Target: Math.two_squares_89
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Two Squares 89
Category: Pure Mathematics
Target: Math.two_squares_89
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Math

/-- The prime `89` is a sum of two squares: `89 = 5 ^ 2 + 8 ^ 2`.
The existence part also follows from Mathlib's `Nat.Prime.sq_add_sq`
(Fermat's two-squares theorem), since `89 % 4 = 1 ≠ 3`. -/
theorem two_squares_89 : Nat.Prime 89 ∧ ∃ a b : ℕ, a ^ 2 + b ^ 2 = 89 :=
  ⟨by norm_num, 5, 8, by norm_num⟩

/-- Restatement via Mathlib's Fermat two-squares theorem `Nat.Prime.sq_add_sq`. -/
theorem two_squares_89_via_mathlib : ∃ a b : ℕ, a ^ 2 + b ^ 2 = 89 := by
  haveI : Fact (Nat.Prime 89) := ⟨by norm_num⟩
  exact Nat.Prime.sq_add_sq (p := 89) (by norm_num)

end Math

