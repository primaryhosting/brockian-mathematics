/-
# Sigma 5040
Category: Riemann Program
Target: Riemann.Robin.sigma_5040
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Sigma 5040
Category: Riemann Program
Target: Riemann.Robin.sigma_5040
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

namespace Riemann.Robin

/-- The sum of divisors of `5040 = 2^4 * 3^2 * 5 * 7` is `19344`.

The proof uses multiplicativity of `σ₁`
(`ArithmeticFunction.isMultiplicative_sigma`) together with the values on the
pairwise coprime prime-power factors `16, 9, 5, 7`. -/

theorem sigma_5040 : ArithmeticFunction.sigma 1 5040 = 19344 := by
  have hm : (ArithmeticFunction.sigma 1).IsMultiplicative :=
    ArithmeticFunction.isMultiplicative_sigma
  have h16 : ArithmeticFunction.sigma 1 16 = 31 := by decide
  have h9 : ArithmeticFunction.sigma 1 9 = 13 := by decide
  have h5 : ArithmeticFunction.sigma 1 5 = 6 := by decide
  have h7 : ArithmeticFunction.sigma 1 7 = 8 := by decide
  have e : (5040 : ℕ) = 16 * (9 * (5 * 7)) := by norm_num
  rw [e, hm.map_mul_of_coprime (by norm_num), hm.map_mul_of_coprime (by norm_num),
    hm.map_mul_of_coprime (by norm_num), h16, h9, h5, h7]
  norm_num

/-- Restatement of `sigma_5040` as an explicit sum over the divisors of `5040`. -/
