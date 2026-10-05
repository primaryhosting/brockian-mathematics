/-
# Two Squares 41
Category: Pure Mathematics
Target: Math.two_squares_41
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Two Squares 41
Category: Pure Mathematics
Target: Math.two_squares_41
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The prime `41` is a sum of two squares: `41 = 4 ^ 2 + 5 ^ 2`.

This is an instance of Fermat's two-squares theorem, available in Mathlib as
`Nat.Prime.sq_add_sq` (a prime `p` with `p % 4 ≠ 3` is a sum of two squares);
here we also record the explicit witnesses. -/
theorem two_squares_41 : Nat.Prime 41 ∧ ∃ a b : ℕ, (41 : ℕ) = a ^ 2 + b ^ 2 :=
  ⟨by norm_num, 4, 5, by norm_num⟩

/-- The same statement obtained from Mathlib's Fermat two-squares theorem
`Nat.Prime.sq_add_sq`, since `41 % 4 = 1 ≠ 3`. -/
theorem two_squares_41_via_mathlib : ∃ a b : ℕ, a ^ 2 + b ^ 2 = 41 :=
  haveI : Fact (Nat.Prime 41) := ⟨by norm_num⟩
  Nat.Prime.sq_add_sq (p := 41) (by norm_num)

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

