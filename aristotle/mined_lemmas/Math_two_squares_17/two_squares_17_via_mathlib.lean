/-
# Two Squares 17
Category: Pure Mathematics
Target: Math.two_squares_17
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Two Squares 17
Category: Pure Mathematics
Target: Math.two_squares_17
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The prime `17` is a sum of two squares: `17 = 1 ^ 2 + 4 ^ 2`. -/

theorem two_squares_17_via_mathlib : ∃ a b : ℕ, a ^ 2 + b ^ 2 = 17 :=
  haveI : Fact (Nat.Prime 17) := ⟨by norm_num⟩
  Nat.Prime.sq_add_sq (p := 17) (by decide)

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

