import Mathlib

/-!
# Catalan Closed
Category: Pure Mathematics
Target: Math.catalan_closed
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Math

/-- Division-free form of the closed formula: `(n + 1) * C_n = binom(2n, n)`. -/

theorem catalan_closed (n : ℕ) : catalan n = Nat.choose (2 * n) n / (n + 1) := by
  rw [← catalan_closed_mul n, Nat.mul_div_cancel_left _ (Nat.succ_pos n)]

/-- The closed formula over the rationals. -/
