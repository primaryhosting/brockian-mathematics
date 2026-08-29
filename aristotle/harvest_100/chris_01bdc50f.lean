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
set_option maxRecDepth 40000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Riemann
namespace Robin

/-- `σ₁(16) = 31`. -/
lemma sigma_16 : ArithmeticFunction.sigma 1 16 = 31 := by decide

/-- `σ₁(9) = 13`. -/
lemma sigma_9 : ArithmeticFunction.sigma 1 9 = 13 := by decide

/-- `σ₁(5) = 6`. -/
lemma sigma_5 : ArithmeticFunction.sigma 1 5 = 6 := by decide

/-- `σ₁(7) = 8`. -/
lemma sigma_7 : ArithmeticFunction.sigma 1 7 = 8 := by decide

/-- The sum of divisors of `5040 = 2^4 * 3^2 * 5 * 7` is `19344`.

`5040` is the largest known exception to Robin's inequality
`σ(n) < e^γ * n * log log n`, whose validity for all `n > 5040` is equivalent to the
Riemann hypothesis.

The proof uses multiplicativity of `σ₁` on the coprime factorization
`5040 = 16 * (9 * (5 * 7))`. -/
theorem sigma_5040 : ArithmeticFunction.sigma 1 5040 = 19344 := by
  have hmul := ArithmeticFunction.isMultiplicative_sigma (k := 1)
  have h1 : (5040 : ℕ) = 16 * (9 * (5 * 7)) := by norm_num
  rw [h1, hmul.map_mul_of_coprime (by norm_num),
    hmul.map_mul_of_coprime (by norm_num),
    hmul.map_mul_of_coprime (by norm_num),
    sigma_16, sigma_9, sigma_5, sigma_7]
  norm_num

end Robin
end Riemann

