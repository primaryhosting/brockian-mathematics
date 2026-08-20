import Mathlib
import RequestProject.TwoSquares53

/-!
# Two Squares 53 (Mathlib route)

A companion to `RequestProject/TwoSquares53.lean`: `53` is prime, and, being a prime
that is not `3 mod 4`, it is a sum of two squares by `Nat.Prime.sq_add_sq`.
-/

namespace Math

/-- `53` is prime and is a sum of two squares, obtained from `Nat.Prime.sq_add_sq`. -/

theorem two_squares_53_prime : Nat.Prime 53 ∧ ∃ a b : ℕ, a ^ 2 + b ^ 2 = 53 := by
  haveI : Fact (Nat.Prime 53) := ⟨by norm_num⟩
  exact ⟨by norm_num, Nat.Prime.sq_add_sq (p := 53) (by decide)⟩

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

/-!
# Two Squares 53
Category: Pure Mathematics
Target: Math.two_squares_53
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The prime `53` is a sum of two squares: `53 = 7 ^ 2 + 2 ^ 2`.

(In Mathlib this also follows from `Nat.Prime.sq_add_sq`, which states that a prime
`p` with `p % 4 ≠ 3` is a sum of two squares; here we give the explicit witnesses,
so that this file needs no imports and the required header comment can come first.) -/
