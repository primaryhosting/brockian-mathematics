import Mathlib

/-!
# Belyi Theorem
Category: Frontier Math
Target: Math2.belyi_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 1000000

open Polynomial IntermediateField

namespace Math2

/-- A complex number is a *rational point* if it lies in the image of `ℚ`. -/

lemma belyiPoly_eval_crit (a b : ℕ) : (belyiPoly a b).eval (belyiCrit a b) = 1 := by
  have hden : ((a:ℚ) + b + 2) ≠ 0 := by positivity
  have h1 : ((a:ℚ) + 1) ≠ 0 := by positivity
  have h2 : ((b:ℚ) + 1) ≠ 0 := by positivity
  simp only [belyiPoly, belyiConst, belyiCrit, eval_mul, eval_C, eval_pow, eval_X, eval_sub,
    eval_one]
  rw [show (1 - ((a:ℚ) + 1) / ((a:ℚ) + b + 2)) = ((b:ℚ) + 1) / ((a:ℚ) + b + 2) by
    field_simp; ring]
  rw [div_pow, div_pow, show a + b + 2 = (a + 1) + (b + 1) by omega, pow_add]
  field_simp

/-- The derivative of the Belyi polynomial, in factored form. -/
