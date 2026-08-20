/-
# Catalan Closed
Category: Pure Mathematics
Target: Math.catalan_closed
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

namespace Math

/-- The `n`th Catalan number equals `C(2n, n) / (n+1)` (exact natural division,
since `n + 1` divides the central binomial coefficient). -/
theorem catalan_closed (n : ℕ) : catalan n = (2 * n).choose n / (n + 1) := by
  simpa [Nat.centralBinom] using catalan_eq_centralBinom_div n

/-- Divisibility making the natural-number division in `catalan_closed` exact. -/
theorem succ_dvd_choose_two_mul (n : ℕ) : (n + 1) ∣ (2 * n).choose n :=
  Nat.succ_dvd_centralBinom n

/-- Rational form of the closed formula: `catalan n = C(2n,n) / (n+1)` in `ℚ`. -/
theorem catalan_closed_rat (n : ℕ) :
    (catalan n : ℚ) = ((2 * n).choose n : ℚ) / (n + 1) := by
  have h : ((n : ℚ) + 1) * (catalan n : ℚ) = ((2 * n).choose n : ℚ) := by
    exact_mod_cast congrArg (fun m : ℕ => (m : ℚ)) (succ_mul_catalan_eq_centralBinom n)
  field_simp
  linarith [h]

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

