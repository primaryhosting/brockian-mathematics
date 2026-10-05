/-
# Two Squares 73
Category: Pure Mathematics
Target: Math.two_squares_73
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Math

/-- The prime `73` is a sum of two squares: `73 = 3 ^ 2 + 8 ^ 2`.

This also follows from Fermat's two-squares theorem, available in Mathlib as
`Nat.Prime.sq_add_sq` (since `73 % 4 = 1 ≠ 3`); see `two_squares_73_via_fermat`. -/
theorem two_squares_73 : Nat.Prime 73 ∧ ∃ a b : ℕ, a ^ 2 + b ^ 2 = 73 := by
  refine ⟨by norm_num, 3, 8, by norm_num⟩

/-- The same statement derived from Mathlib's form of Fermat's two-squares theorem,
`Nat.Prime.sq_add_sq`. -/
theorem two_squares_73_via_fermat : ∃ a b : ℕ, a ^ 2 + b ^ 2 = 73 := by
  have : Fact (Nat.Prime 73) := ⟨by norm_num⟩
  obtain ⟨a, b, hab⟩ := Nat.Prime.sq_add_sq (p := 73) (by norm_num)
  exact ⟨a, b, hab⟩

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

