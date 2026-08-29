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

set_option grind.warning false

namespace Riemann.Robin

/-- `σ₁(2^4) = 1 + 2 + 4 + 8 + 16 = 31`. -/
lemma sigma_one_sixteen : ArithmeticFunction.sigma 1 16 = 31 := by decide

/-- `σ₁(3^2) = 1 + 3 + 9 = 13`. -/
lemma sigma_one_nine : ArithmeticFunction.sigma 1 9 = 13 := by decide

/-- `σ₁(5) = 1 + 5 = 6`. -/
lemma sigma_one_five : ArithmeticFunction.sigma 1 5 = 6 := by decide

/-- `σ₁(7) = 1 + 7 = 8`. -/
lemma sigma_one_seven : ArithmeticFunction.sigma 1 7 = 8 := by decide

/--
The sum of divisors of `5040 = 2^4 * 3^2 * 5 * 7` equals `19344`.

The proof uses the multiplicativity of `σ₁` together with the prime factorization
of `5040`:  `σ₁(5040) = σ₁(16) · σ₁(9) · σ₁(5) · σ₁(7) = 31 · 13 · 6 · 8 = 19344`.

`5040` is the largest known exception to Robin's inequality
`σ(n) < e^γ · n · log log n`, which for `n > 5040` is equivalent to the
Riemann hypothesis.
-/
theorem sigma_5040 : ArithmeticFunction.sigma 1 5040 = 19344 := by
  have hmul := ArithmeticFunction.isMultiplicative_sigma (k := 1)
  have h1 : (5040 : ℕ) = 16 * (9 * (5 * 7)) := by norm_num
  have e1 : ArithmeticFunction.sigma 1 (5 * 7) =
      ArithmeticFunction.sigma 1 5 * ArithmeticFunction.sigma 1 7 :=
    hmul.map_mul_of_coprime (by decide)
  have e2 : ArithmeticFunction.sigma 1 (9 * (5 * 7)) =
      ArithmeticFunction.sigma 1 9 * ArithmeticFunction.sigma 1 (5 * 7) :=
    hmul.map_mul_of_coprime (by decide)
  have e3 : ArithmeticFunction.sigma 1 (16 * (9 * (5 * 7))) =
      ArithmeticFunction.sigma 1 16 * ArithmeticFunction.sigma 1 (9 * (5 * 7)) :=
    hmul.map_mul_of_coprime (by decide)
  rw [h1, e3, e2, e1, sigma_one_sixteen, sigma_one_nine, sigma_one_five, sigma_one_seven]

end Riemann.Robin

