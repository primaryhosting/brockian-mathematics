import RequestProject.BelyiPoly

/-!
# Belyi polynomials for finite sets of rational points

A polynomial `f ∈ ℚ[X]` is *Belyi* if it is non-constant and all of its finite critical values
(computed over `ℂ`) lie in `{0, 1}`; viewed as a map `ℙ¹ → ℙ¹` such an `f` is ramified only
above `{0, 1, ∞}`.

The main result of this file is `Math2.exists_belyiPolynomial_of_rat`: for every finite set of
rational numbers there is a Belyi polynomial taking each of them to `0` or `1`.
-/

set_option maxRecDepth 8000

namespace Math2

open Polynomial

/-- `f` is a Belyi polynomial: non-constant, with all finite critical values in `{0, 1}`. -/

lemma belyiPoly_derivative (a b : ℕ) :
    derivative (belyiPoly (a + 1) (b + 1)) =
      C (bcoef (a + 1) (b + 1)) *
        (X ^ a * (1 - X) ^ b * (C ((a : ℚ) + 1) - C ((a : ℚ) + (b : ℚ) + 2) * X)) := by
  unfold belyiPoly
  simp only [derivative_mul, derivative_pow, derivative_X, derivative_C, derivative_sub,
    derivative_one, zero_mul, zero_add, mul_one, Nat.add_sub_cancel]
  simp only [Nat.cast_add, Nat.cast_one, C_add, C_1, map_ofNat]
  ring

section CriticalValues

/-- Evaluating a rational polynomial at a rational point, seen inside `ℂ`. -/
