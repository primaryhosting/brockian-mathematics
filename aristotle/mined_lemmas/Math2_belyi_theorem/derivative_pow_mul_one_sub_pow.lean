import Mathlib

/-!
# Belyi Theorem
Category: Frontier Math
Target: Math2.belyi_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Polynomial
open scoped IntermediateField

namespace Math2

/-- A *Belyi map* (in the genus-zero, polynomial model): a nonconstant polynomial with
rational coefficients, viewed as a morphism `ℙ¹ → ℙ¹` defined over `ℚ`, all of whose
finite critical values lie in `{0, 1}`.  Being a polynomial, such a map is totally
ramified over `∞`, so it is ramified only above `{0, 1, ∞}`. -/

theorem derivative_pow_mul_one_sub_pow (m n : ℕ) :
    derivative ((X : ℚ[X]) ^ (m + 1) * (1 - X) ^ (n + 1)) =
      X ^ m * (1 - X) ^ n * (C ((m : ℚ) + 1) - C ((m : ℚ) + (n : ℚ) + 2) * X) := by
  simp only [derivative_mul, derivative_pow, derivative_X, derivative_sub, derivative_one,
    Polynomial.C_add, Polynomial.C_1, map_ofNat]
  push_cast
  simp only [Polynomial.C_add, Polynomial.C_1]
  ring

