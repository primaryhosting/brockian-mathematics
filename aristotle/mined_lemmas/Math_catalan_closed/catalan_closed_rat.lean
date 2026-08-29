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

theorem catalan_closed_rat (n : ℕ) :
    (catalan n : ℚ) = (Nat.choose (2 * n) n : ℚ) / (n + 1) := by
  have h : ((n : ℚ) + 1) * (catalan n : ℚ) = (Nat.choose (2 * n) n : ℚ) := by
    exact_mod_cast catalan_closed_mul n
  have hne : ((n : ℚ) + 1) ≠ 0 := by positivity
  field_simp
  linarith [h]

end Math

