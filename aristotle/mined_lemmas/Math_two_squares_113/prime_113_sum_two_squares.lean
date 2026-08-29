import Mathlib
import RequestProject.TwoSquares113

/-!
# Two Squares 113 (Mathlib restatement)

Restatement of `Math.two_squares_113` using Mathlib's `Nat.Prime`.
-/

namespace Math

/-- `Math.IsPrimeNat` agrees with Mathlib's `Nat.Prime`. -/

theorem prime_113_sum_two_squares :
    Nat.Prime 113 ∧ ∃ a b : Nat, (113 : Nat) = a ^ 2 + b ^ 2 :=
  ⟨(isPrimeNat_iff_prime 113).mp two_squares_113.1, two_squares_113.2⟩

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
# Two Squares 113
Category: Pure Mathematics
Target: Math.two_squares_113
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: Lean requires `import` commands to precede every other command, including
-- module doc comments. Since this file must begin with the header above, it is written
-- without imports, using only Lean core. A Mathlib-flavoured restatement (in terms of
-- `Nat.Prime`) is derived from this theorem in `RequestProject/TwoSquares113Mathlib.lean`.

namespace Math

/-- Primality of a natural number, stated without Mathlib: `p` is at least `2` and its
only divisors are `1` and `p`. -/
