/-
# Two Squares 73 (Mathlib phrasing)
Companion to `RequestProject/TwoSquares73.lean`, stating primality via `Nat.Prime`.
-/

import Mathlib

namespace Math

/-- The prime `73` is a sum of two squares: `73 = 3 ^ 2 + 8 ^ 2`. -/

theorem two_squares_73_nat_prime : Nat.Prime 73 ∧ ∃ a b : ℕ, 73 = a ^ 2 + b ^ 2 :=
  ⟨by norm_num, 3, 8, by norm_num⟩

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
# Two Squares 73
Category: Pure Mathematics
Target: Math.two_squares_73
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- **73 is a prime that is a sum of two squares.**

Primality is spelled out directly (`1 < 73` together with: every divisor of `73`
is `1` or `73`), and the two-square decomposition is `73 = 3 ^ 2 + 8 ^ 2`.

The statement is phrased without any imports so that the header comment above can
be the first thing in the file; the Mathlib-flavoured version, stated with
`Nat.Prime`, is `Math.two_squares_73_nat_prime` in `RequestProject/TwoSquares73Mathlib.lean`. -/
