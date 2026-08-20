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

theorem belyiPush_natDegree (m n : ℕ) : 0 < (belyiPush (m + 1) (n + 1)).natDegree := by
  have hc : (((m : ℚ) + 1 + ((n : ℚ) + 1)) ^ ((m + 1) + (n + 1))) /
      (((m : ℚ) + 1) ^ (m + 1) * ((n : ℚ) + 1) ^ (n + 1)) ≠ 0 := by positivity
  have hX : ((X : ℚ[X]) ^ (m + 1)) ≠ 0 := pow_ne_zero _ X_ne_zero
  have h1X : ((1 - X : ℚ[X]) ^ (n + 1)) ≠ 0 := by
    refine pow_ne_zero _ fun h => ?_
    have := congrArg (Polynomial.eval (0 : ℚ)) h
    simp at this
  unfold belyiPush
  rw [natDegree_C_mul (by push_cast; exact_mod_cast hc), natDegree_mul hX h1X]
  have h1 : (1 - X : ℚ[X]).natDegree = 1 := by compute_degree!
  simp [natDegree_pow, h1]

/-- Weighted AM–GM: `x^a (1-x)^b ≤ a^a b^b / (a+b)^(a+b)` on `[0,1]`. -/
