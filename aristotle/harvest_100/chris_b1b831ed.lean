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

open ArithmeticFunction

/-- `σ₁(2^4) = 31`. -/
lemma sigma_one_two_pow_four : ArithmeticFunction.sigma 1 (2 ^ 4) = 31 := by
  rw [sigma_one_apply_prime_pow Nat.prime_two]
  decide

/-- `σ₁(3^2) = 13`. -/
lemma sigma_one_three_pow_two : ArithmeticFunction.sigma 1 (3 ^ 2) = 13 := by
  rw [sigma_one_apply_prime_pow Nat.prime_three]
  decide

/-- `σ₁(5) = 6`. -/
lemma sigma_one_five : ArithmeticFunction.sigma 1 5 = 6 := by
  have h : (5 : ℕ) = 5 ^ 1 := by norm_num
  rw [h, sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5)]
  decide

/-- `σ₁(7) = 8`. -/
lemma sigma_one_seven : ArithmeticFunction.sigma 1 7 = 8 := by
  have h : (7 : ℕ) = 7 ^ 1 := by norm_num
  rw [h, sigma_one_apply_prime_pow (by norm_num : Nat.Prime 7)]
  decide

/-- The sum of divisors of `5040 = 2^4 * 3^2 * 5 * 7` equals `19344`.
`5040` is the largest known exception to Robin's inequality. -/
theorem sigma_5040 : ArithmeticFunction.sigma 1 5040 = 19344 := by
  have h5040 : (5040 : ℕ) = 2 ^ 4 * (3 ^ 2 * (5 * 7)) := by norm_num
  have hmul := isMultiplicative_sigma (k := 1)
  rw [h5040, hmul.map_mul_of_coprime (by norm_num),
    hmul.map_mul_of_coprime (by norm_num),
    hmul.map_mul_of_coprime (by norm_num),
    sigma_one_two_pow_four, sigma_one_three_pow_two, sigma_one_five, sigma_one_seven]
  norm_num

end Riemann.Robin

