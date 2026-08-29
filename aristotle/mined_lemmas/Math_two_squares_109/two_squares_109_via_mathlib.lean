/-
# Two Squares 109
Category: Pure Mathematics
Target: Math.two_squares_109
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Two Squares 109
Category: Pure Mathematics
Target: Math.two_squares_109
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The prime `109` is a sum of two squares: `109 = 10 ^ 2 + 3 ^ 2`.

Mathlib's `Nat.Prime.sq_add_sq` provides this abstractly for any prime `p % 4 ≠ 3`;
here the explicit witnesses are exhibited. -/

theorem two_squares_109_via_mathlib : ∃ a b : ℕ, 109 = a ^ 2 + b ^ 2 := by
  have hp : Nat.Prime 109 := by norm_num
  obtain ⟨a, b, hab⟩ := hp.sq_add_sq (by norm_num)
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

