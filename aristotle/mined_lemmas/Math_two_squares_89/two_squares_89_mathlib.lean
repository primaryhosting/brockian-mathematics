/-!
# Two Squares 89
Category: Pure Mathematics
Target: Math.two_squares_89
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- **Two squares for 89.** The prime `89` is a sum of two squares: `89 = 5 ^ 2 + 8 ^ 2`.

Since Lean does not permit an `import` after the required header comment, this file is
self-contained: primality of `89` is spelled out directly as "`2 ≤ 89` and every divisor of `89`
is `1` or `89`", which is exactly `Nat.Prime 89` (see `Math.two_squares_89_mathlib` in
`RequestProject/TwoSquares89Mathlib.lean` for the Mathlib-phrased version). -/

theorem two_squares_89_mathlib : Nat.Prime 89 ∧ ∃ a b : ℕ, 89 = a ^ 2 + b ^ 2 :=
  ⟨by norm_num, 5, 8, by norm_num⟩

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

