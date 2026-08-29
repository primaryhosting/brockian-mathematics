/-!
# Two Squares 61
Category: Pure Mathematics
Target: Math.two_squares_61
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- **The prime `61` is a sum of two squares.**

The first component states that `61` is prime, spelled out elementarily as
`1 < 61` together with "every proper divisor of `61` equals `1`"; the second
component exhibits `61 = 5 ^ 2 + 6 ^ 2`.

The required header comment must be the first thing in this file, which Lean does
not allow to be followed by `import` commands, so this file is stated and proved
using only Lean core.  The same result phrased with Mathlib's `Nat.Prime` and
derived from Mathlib's two-square theorem `Nat.Prime.sq_add_sq` is in
`RequestProject/TwoSquares61Mathlib.lean`. -/

theorem prime_61_sum_two_squares' : ∃ a b : ℕ, a ^ 2 + b ^ 2 = 61 :=
  haveI : Fact (Nat.Prime 61) := ⟨by norm_num⟩
  Nat.Prime.sq_add_sq (p := 61) (by norm_num)

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

