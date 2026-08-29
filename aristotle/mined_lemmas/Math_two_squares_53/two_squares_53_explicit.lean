/-!
# Two Squares 53
Category: Pure Mathematics
Target: Math.two_squares_53
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The prime `53` is a sum of two squares.

Since Lean requires `import` commands to precede every other command in a file,
and the header comment above must be the first thing in this file, this module
is written in pure core Lean (no imports). Primality of `53` is therefore
spelled out directly: `1 < 53` and every divisor of `53` is `1` or `53`.
The Mathlib-flavoured version, stated with `Nat.Prime` and deduced from
Mathlib's Fermat's Christmas theorem `Nat.Prime.sq_add_sq`, is in
`RequestProject/MathMathlib.lean`.

The two squares are `53 = 7 ^ 2 + 2 ^ 2`. -/

theorem two_squares_53_explicit : (7 : ℕ) ^ 2 + 2 ^ 2 = 53 := by norm_num

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

