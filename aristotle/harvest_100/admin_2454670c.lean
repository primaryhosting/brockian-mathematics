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

/-- The sum of divisors of `5040 = 2^4 * 3^2 * 5 * 7` equals `19344`.

`5040` is the largest known exception to Robin's inequality
`sigma n < e^gamma * n * log (log n)`, whose validity for all `n > 5040`
is equivalent to the Riemann hypothesis.

The proof uses multiplicativity of `sigma`, splitting `5040` into its
pairwise coprime prime-power factors. -/
theorem sigma_5040 : ArithmeticFunction.sigma 1 5040 = 19344 := by
  have hmul := ArithmeticFunction.isMultiplicative_sigma (k := 1)
  have h16 : ArithmeticFunction.sigma 1 16 = 31 := by
    rw [ArithmeticFunction.sigma_one_apply]; decide
  have h9 : ArithmeticFunction.sigma 1 9 = 13 := by
    rw [ArithmeticFunction.sigma_one_apply]; decide
  have h5 : ArithmeticFunction.sigma 1 5 = 6 := by
    rw [ArithmeticFunction.sigma_one_apply]; decide
  have h7 : ArithmeticFunction.sigma 1 7 = 8 := by
    rw [ArithmeticFunction.sigma_one_apply]; decide
  have hfac : (5040 : ℕ) = 16 * (9 * (5 * 7)) := by norm_num
  rw [hfac, hmul.map_mul_of_coprime (by norm_num),
    hmul.map_mul_of_coprime (by norm_num),
    hmul.map_mul_of_coprime (by norm_num), h16, h9, h5, h7]
  norm_num

end Riemann.Robin

