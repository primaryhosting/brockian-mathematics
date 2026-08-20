/-!
# Sigma 5040
Category: Riemann Program
Target: Riemann.Robin.sigma_5040
Statement: The sum of divisors satisfies ArithmeticFunction.sigma 1 5040 = 19344. (5040 = 2^4 * 3^2 * 5 * 7 is the LARGEST known exception to Robin's inequality sigma(n) < e^gamma * n * log log n, which for n > 5040 is EQUIVALENT to the Riemann hypothesis.)
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-
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
set_option maxRecDepth 10000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Riemann.Robin

/-- The sum of divisors of `5040 = 2^4 * 3^2 * 5 * 7` is
`31 * 13 * 6 * 8 = 19344`.

`5040` is the largest known exception to Robin's inequality
`σ(n) < e^γ * n * log log n`, whose validity for all `n > 5040` is
equivalent to the Riemann hypothesis.

The proof uses multiplicativity of `σ₁` together with the values on the
prime power factors `16`, `9`, `5`, `7`. -/
theorem sigma_5040 : ArithmeticFunction.sigma 1 5040 = 19344 := by
  have hm := ArithmeticFunction.isMultiplicative_sigma (k := 1)
  have h16 : ArithmeticFunction.sigma 1 16 = 31 := by
    simp [ArithmeticFunction.sigma_apply]; rfl
  have h9 : ArithmeticFunction.sigma 1 9 = 13 := by
    simp [ArithmeticFunction.sigma_apply]; rfl
  have h5 : ArithmeticFunction.sigma 1 5 = 6 := by
    simp [ArithmeticFunction.sigma_apply]; rfl
  have h7 : ArithmeticFunction.sigma 1 7 = 8 := by
    simp [ArithmeticFunction.sigma_apply]; rfl
  have e35 : ArithmeticFunction.sigma 1 35 = 48 := by
    have := hm.map_mul_of_coprime (m := 5) (n := 7) (by norm_num)
    simpa [h5, h7] using this
  have e315 : ArithmeticFunction.sigma 1 315 = 624 := by
    have := hm.map_mul_of_coprime (m := 9) (n := 35) (by norm_num)
    norm_num [h9, e35] at this
    simpa using this
  have := hm.map_mul_of_coprime (m := 16) (n := 315) (by norm_num)
  norm_num [h16, e315] at this
  simpa using this

end Riemann.Robin

