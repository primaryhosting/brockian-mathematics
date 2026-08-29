/-!
# Two Squares 41
Category: Pure Mathematics
Target: Math.two_squares_41
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- **The prime 41 is a sum of two squares.**

`41` is prime (it is at least `2` and its only divisors are `1` and `41`) and
`41 = 4 ^ 2 + 5 ^ 2`.

The fixed header comment above must be the first thing in this file, which makes an
`import` line illegal here, so primality is spelled out directly and the proof uses
only Lean's core library.  See `RequestProject/MathMathlib.lean` for the same fact
stated with Mathlib's `Nat.Prime` and derived from `Nat.Prime.sq_add_sq`. -/

theorem two_squares_41_via_fermat : ∃ a b : ℕ, a ^ 2 + b ^ 2 = 41 :=
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

