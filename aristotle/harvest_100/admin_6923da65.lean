import Mathlib

/-!
# Two Squares 101
Category: Pure Mathematics
Target: Math.two_squares_101
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The prime 101 is a sum of two squares: `101 = 10 ^ 2 + 1 ^ 2`.

Mathlib also provides the general fact
`Nat.Prime.sq_add_sq : [Fact p.Prime] → p % 4 ≠ 3 → ∃ a b, a ^ 2 + b ^ 2 = p`
(Fermat's two-squares theorem), which applies here since `101 % 4 = 1`;
see `two_squares_101_via_mathlib` below. -/
theorem two_squares_101 : Nat.Prime 101 ∧ ∃ a b : ℕ, 101 = a ^ 2 + b ^ 2 :=
  ⟨by norm_num, 10, 1, by norm_num⟩

/-- The same statement derived from Mathlib's Fermat two-squares theorem
`Nat.Prime.sq_add_sq`. -/
theorem two_squares_101_via_mathlib : ∃ a b : ℕ, 101 = a ^ 2 + b ^ 2 := by
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

