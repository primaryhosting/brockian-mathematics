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

theorem belyiPush_eval_ratio (m n : ℕ) :
    (belyiPush (m + 1) (n + 1)).eval (((m : ℚ) + 1) / ((m : ℚ) + (n : ℚ) + 2)) = 1 := by
  have ha : ((m : ℚ) + 1) ≠ 0 := by positivity
  have hb : ((n : ℚ) + 1) ≠ 0 := by positivity
  have hs : ((m : ℚ) + (n : ℚ) + 2) ≠ 0 := by positivity
  unfold belyiPush
  simp only [eval_mul, eval_C, eval_pow, eval_X, eval_sub, eval_one]
  push_cast
  have h1 : (1 : ℚ) - ((m : ℚ) + 1) / ((m : ℚ) + (n : ℚ) + 2)
      = ((n : ℚ) + 1) / ((m : ℚ) + (n : ℚ) + 2) := by field_simp; ring
  rw [h1, div_pow, div_pow, show ((m : ℚ) + 1 + ((n : ℚ) + 1)) = ((m : ℚ) + (n : ℚ) + 2) by ring,
    pow_add]
  field_simp

/-- Every critical value of `belyiPush (m+1) (n+1)` lies in `{0,1}`. -/
