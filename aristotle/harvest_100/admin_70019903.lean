/-
# Two Squares 13
Category: Pure Mathematics
Target: Math.two_squares_13
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Two Squares 13
Category: Pure Mathematics
Target: Math.two_squares_13
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Math

/-- The prime 13 is a sum of two squares: `13 = 2^2 + 3^2`. -/
theorem two_squares_13 : Nat.Prime 13 ∧ ∃ a b : ℕ, (13 : ℕ) = a ^ 2 + b ^ 2 := by
  refine ⟨by norm_num, 2, 3, by norm_num⟩

end Math

