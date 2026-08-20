/-!
# Two Squares 41
Category: Pure Mathematics
Target: Math.two_squares_41
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- **The prime 41 is a sum of two squares.**

Since Lean requires `import` commands to precede every other piece of syntax except
plain comments, and this file must begin with the module docstring above, the statement
is phrased using only the core-`Nat` unfolding of primality: `41` is greater than `1`
and its only divisors are `1` and `41`.  The witnesses for the two squares are
`41 = 4 ^ 2 + 5 ^ 2`.  (A Mathlib-flavoured restatement using `Nat.Prime` is proved in
`RequestProject.TwoSquares41Prime`.) -/

theorem two_squares_41_prime : Nat.Prime 41 ∧ ∃ a b : ℕ, 41 = a ^ 2 + b ^ 2 := by
  obtain ⟨⟨h1, hdvd⟩, hsq⟩ := two_squares_41
  exact ⟨Nat.prime_def.mpr ⟨h1, fun m hm => (hdvd m hm).imp id id⟩, hsq⟩

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

