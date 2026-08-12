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

namespace Math

/-- The `n`th Catalan number equals `C(2n, n) / (n + 1)` (natural-number division,
which is exact here since `n + 1` divides the central binomial coefficient). -/
theorem catalan_closed (n : ℕ) : catalan n = Nat.choose (2 * n) n / (n + 1) :=
  catalan_eq_centralBinom_div n

/-- Exact (division-free) form: `(n + 1) * catalan n = C(2n, n)`. -/
theorem succ_mul_catalan_eq_choose (n : ℕ) :
    (n + 1) * catalan n = Nat.choose (2 * n) n := by
  have h := succ_mul_catalan_eq_centralBinom n
  simpa [Nat.centralBinom] using h

end Math

