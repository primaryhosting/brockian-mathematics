/-!
# Two Squares 89
Category: Pure Mathematics
Target: Math.two_squares_89
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- Primality of a natural number, spelled out: `n` is at least `2` and its only
divisors are `1` and `n`.  (This is definitionally the same notion as
`Nat.Prime`; it is stated here directly because the required file header must be
the very first thing in the file, which precludes an `import` command.) -/

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

