/-
# Catalan Closed
Category: Pure Mathematics
Target: Math.catalan_closed
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-- Division-free form of the closed formula: `(n + 1) * catalan n = C(2n, n)`. -/
theorem catalan_closed_mul (n : ℕ) : (n + 1) * catalan n = Nat.choose (2 * n) n := by
  simpa [Nat.centralBinom, two_mul] using succ_mul_catalan_eq_centralBinom n

/-- The `n`th Catalan number equals `C(2n, n) / (n + 1)` (natural-number division, which is
exact here since `n + 1` divides `C(2n, n)`). -/
theorem catalan_closed (n : ℕ) : catalan n = Nat.choose (2 * n) n / (n + 1) := by
  rw [← catalan_closed_mul n, Nat.mul_div_cancel_left _ n.succ_pos]

/-- Rational-valued version of the closed formula, where the division is genuine division. -/
theorem catalan_closed_rat (n : ℕ) : (catalan n : ℚ) = (Nat.choose (2 * n) n : ℚ) / (n + 1) := by
  have h : ((n : ℚ) + 1) * (catalan n : ℚ) = (Nat.choose (2 * n) n : ℚ) := by
    exact_mod_cast congrArg (fun m : ℕ => (m : ℚ)) (catalan_closed_mul n)
  rw [eq_div_iff (by positivity)]
  linarith [h]

end Math

