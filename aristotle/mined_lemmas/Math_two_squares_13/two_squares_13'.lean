import Mathlib
/-!
# Two Squares 13
Category: Pure Mathematics
Target: Math.two_squares_13
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- **Two squares for 13.** The prime `13` is a sum of two squares, namely
`13 = 2 ^ 2 + 3 ^ 2`.

Mathlib's general result is Fermat's two-squares theorem, `Nat.Prime.sq_add_sq`
(a prime `p` with `p % 4 ≠ 3` is a sum of two squares); for the concrete prime
`13` we exhibit the witnesses directly. -/

theorem two_squares_13' : ∃ a b : ℕ, a ^ 2 + b ^ 2 = 13 :=
  haveI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  Nat.Prime.sq_add_sq (p := 13) (by norm_num)

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

