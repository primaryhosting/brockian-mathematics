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

import Mathlib

/-!
# Two Squares 53
Category: Pure Mathematics
Target: Math.two_squares_53
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- `53` is prime and is a sum of two squares: `53 = 7 ^ 2 + 2 ^ 2`.

The existence of such a representation for any prime `p % 4 = 1` is
`Nat.Prime.sq_add_sq` in Mathlib; here we also exhibit the witnesses explicitly. -/

theorem two_squares_53_via_mathlib : ∃ a b : ℕ, a ^ 2 + b ^ 2 = 53 :=
  haveI : Fact (Nat.Prime 53) := ⟨by norm_num⟩
  Nat.Prime.sq_add_sq (p := 53) (by norm_num)

end Math

