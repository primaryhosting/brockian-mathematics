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

set_option grind.warning false

namespace Riemann.Robin

/-- The sum of divisors of `5040 = 2^4 * 3^2 * 5 * 7` equals `19344`.

The proof uses the multiplicativity of `σ₁` on the coprime factorization
`5040 = 16 * (9 * (5 * 7))`, together with the values
`σ₁(16) = 31`, `σ₁(9) = 13`, `σ₁(5) = 6`, `σ₁(7) = 8`. -/
theorem sigma_5040 : ArithmeticFunction.sigma 1 5040 = 19344 := by
  have hm := ArithmeticFunction.isMultiplicative_sigma (k := 1)
  have h1 : (5040 : ℕ) = 16 * (9 * (5 * 7)) := by norm_num
  have e16 : ArithmeticFunction.sigma 1 16 = 31 := by
    simp [ArithmeticFunction.sigma_apply]; rfl
  have e9 : ArithmeticFunction.sigma 1 9 = 13 := by
    simp [ArithmeticFunction.sigma_apply]; rfl
  have e5 : ArithmeticFunction.sigma 1 5 = 6 := by
    simp [ArithmeticFunction.sigma_apply]; rfl
  have e7 : ArithmeticFunction.sigma 1 7 = 8 := by
    simp [ArithmeticFunction.sigma_apply]; rfl
  rw [h1, hm.map_mul_of_coprime (by decide), hm.map_mul_of_coprime (by decide),
    hm.map_mul_of_coprime (by decide), e16, e9, e5, e7]
  norm_num

end Riemann.Robin

