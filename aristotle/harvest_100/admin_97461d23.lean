import Mathlib
/-!
# Catalan Closed
Category: Pure Mathematics
Target: Math.catalan_closed
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The `n`-th Catalan number equals `C(2n, n) / (n + 1)` (natural division, which is exact
here since `n + 1` divides the central binomial coefficient).
This is Mathlib's `catalan_eq_centralBinom_div`, with `Nat.centralBinom n = (2 * n).choose n`
unfolded. -/
theorem catalan_closed (n : ℕ) : catalan n = Nat.choose (2 * n) n / (n + 1) :=
  catalan_eq_centralBinom_div n

/-- Division-free form: `(n + 1) * catalan n = C(2n, n)`. -/
theorem succ_mul_catalan_closed (n : ℕ) : (n + 1) * catalan n = Nat.choose (2 * n) n :=
  succ_mul_catalan_eq_centralBinom n

/-- Rational form of the closed formula: `catalan n = C(2n, n) / (n + 1)` in `ℚ`. -/
theorem catalan_closed_rat (n : ℕ) :
    (catalan n : ℚ) = (Nat.choose (2 * n) n : ℚ) / (n + 1) := by
  have h : catalan n * (n + 1) = Nat.choose (2 * n) n := by
    rw [mul_comm]; exact succ_mul_catalan_closed n
  rw [eq_div_iff (by positivity)]
  exact_mod_cast h

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

