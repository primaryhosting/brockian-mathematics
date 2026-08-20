/-
# Two Squares 61
Category: Pure Mathematics
Target: Math.two_squares_61
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Two Squares 61
Category: Pure Mathematics
Target: Math.two_squares_61
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- `61` is prime and is a sum of two squares (explicitly, `61 = 5 ^ 2 + 6 ^ 2`).

The existence part is also an instance of Fermat's two-squares theorem, available in
Mathlib as `Nat.Prime.sq_add_sq` (see `Math.two_squares_61_of_mathlib` below). -/

theorem two_squares_61_of_mathlib : ∃ a b : ℕ, a ^ 2 + b ^ 2 = 61 := by
  haveI : Fact (Nat.Prime 61) := ⟨by norm_num⟩
  exact Nat.Prime.sq_add_sq (by norm_num)

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

