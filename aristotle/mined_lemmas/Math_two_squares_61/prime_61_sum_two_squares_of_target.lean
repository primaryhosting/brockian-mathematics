/-!
# Two Squares 61
Category: Pure Mathematics
Target: Math.two_squares_61
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- **Two squares for 61.** The number `61` is prime -- its only divisors are `1` and `61`,
and it is at least `2` -- and it is a sum of two squares, namely `61 = 5 ^ 2 + 6 ^ 2`.

Primality is spelled out elementarily here (`2 ≤ 61` together with the divisor condition)
so that this file needs no imports; the file `TwoSquares61Mathlib.lean` records the same
result phrased with Mathlib's `Nat.Prime`, together with the equivalence of the two
formulations. -/

theorem prime_61_sum_two_squares_of_target :
    Nat.Prime 61 ∧ ∃ a b : ℕ, 61 = a ^ 2 + b ^ 2 :=
  ⟨prime_61_iff.mp two_squares_61.1, two_squares_61.2⟩

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

