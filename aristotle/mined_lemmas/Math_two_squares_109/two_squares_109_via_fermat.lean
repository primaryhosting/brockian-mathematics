import Mathlib

/-!
# Two Squares 109 (Mathlib version)

Mathlib-based companion to `RequestProject/TwoSquares109.lean`: the prime `109`
is a sum of two squares, both by an explicit witness and via Mathlib's
`Nat.Prime.sq_add_sq` (Fermat's theorem on sums of two squares).
-/

namespace Math

/-- `109` is prime and `109 = 10 ^ 2 + 3 ^ 2`. -/

theorem two_squares_109_via_fermat : ∃ a b : ℕ, a ^ 2 + b ^ 2 = 109 := by
  haveI : Fact (Nat.Prime 109) := ⟨by norm_num⟩
  exact Nat.Prime.sq_add_sq (p := 109) (by norm_num)

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
# Two Squares 109
Category: Pure Mathematics
Target: Math.two_squares_109
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: Lean 4 requires `import` commands to precede every other command, including
-- module doc comments such as the header above. To keep the header at the very top of
-- this file, the target theorem is proved here self-containedly (core Lean only), with
-- primality of 109 spelled out explicitly. The companion file
-- `RequestProject/TwoSquares109Mathlib.lean` derives the same statement with Mathlib,
-- using `Nat.Prime.sq_add_sq` (Fermat's theorem on sums of two squares).

namespace Math

/-- **The prime 109 is a sum of two squares**: `109 = 10 ^ 2 + 3 ^ 2`.
Primality is stated as `2 ≤ 109` together with the fact that every divisor of `109`
is `1` or `109`. -/
