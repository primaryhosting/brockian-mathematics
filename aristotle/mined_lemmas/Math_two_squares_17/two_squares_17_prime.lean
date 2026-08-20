/-!
# Two Squares 17
Category: Pure Mathematics
Target: Math.two_squares_17
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- **Two squares for 17.**  The number `17` is prime (its only divisors are `1` and `17`)
and it is a sum of two squares, namely `17 = 1 ^ 2 + 4 ^ 2`.

Note: the required header comment above must be the very first thing in the file, and Lean
requires `import` commands to precede every other command, so this file is stated with the
core `Nat` API only.  A companion file `RequestProject/TwoSquares17Mathlib.lean` states the
same result using Mathlib's `Nat.Prime`. -/

theorem two_squares_17_prime :
    Nat.Prime 17 ∧ ∃ a b : ℕ, (17 : ℕ) = a ^ 2 + b ^ 2 :=
  ⟨by norm_num, 1, 4, by norm_num⟩

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

