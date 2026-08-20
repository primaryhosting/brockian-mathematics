/-
# Two Squares 101
Category: Pure Mathematics
Target: Math.two_squares_101
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Math

/-- The prime `101` is a sum of two squares: `101 = 1 ^ 2 + 10 ^ 2`.

The existence part also follows from Mathlib's `Nat.Prime.sq_add_sq`
(Fermat's two-squares theorem, since `101 % 4 = 1 ≠ 3`); see
`Math.two_squares_101_via_fermat` below. -/
theorem two_squares_101 : Nat.Prime 101 ∧ ∃ a b : ℕ, 101 = a ^ 2 + b ^ 2 :=
  ⟨by norm_num, 1, 10, by norm_num⟩

/-- The same existence statement obtained from Mathlib's `Nat.Prime.sq_add_sq`. -/
theorem two_squares_101_via_fermat : ∃ a b : ℕ, 101 = a ^ 2 + b ^ 2 := by
  haveI : Fact (Nat.Prime 101) := ⟨by norm_num⟩
  obtain ⟨a, b, hab⟩ := Nat.Prime.sq_add_sq (p := 101) (by norm_num)
  exact ⟨a, b, hab.symm⟩

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

