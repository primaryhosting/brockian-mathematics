/-
# Sigma 5040
Category: Riemann Program
Target: Riemann.Robin.sigma_5040
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Riemann.Robin

/-- The sum of divisors of `5040 = 2^4 * 3^2 * 5 * 7` equals `19344`.

The proof uses multiplicativity of `σ₁`: since `5040 = 16 * 9 * 5 * 7` with pairwise
coprime factors, `σ₁(5040) = 31 * 13 * 6 * 8 = 19344`. -/

theorem sigma_5040 : ArithmeticFunction.sigma 1 5040 = 19344 := by
  have hmul := ArithmeticFunction.isMultiplicative_sigma (k := 1)
  have e1 : (5040 : ℕ) = 16 * 315 := by norm_num
  have e2 : (315 : ℕ) = 9 * 35 := by norm_num
  have e3 : (35 : ℕ) = 5 * 7 := by norm_num
  rw [e1, hmul.map_mul_of_coprime (by decide), e2, hmul.map_mul_of_coprime (by decide),
    e3, hmul.map_mul_of_coprime (by decide)]
  simp [ArithmeticFunction.sigma_one_apply]
  decide

end Riemann.Robin

