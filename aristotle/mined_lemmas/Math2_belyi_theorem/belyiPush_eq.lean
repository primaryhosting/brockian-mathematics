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

theorem belyiPush_eq (m n : ℕ) : belyiPush (m + 1) (n + 1) =
    C ((((m : ℚ) + 1 + ((n : ℚ) + 1)) ^ ((m + 1) + (n + 1))) /
        (((m : ℚ) + 1) ^ (m + 1) * ((n : ℚ) + 1) ^ (n + 1)))
      * ((X : ℚ[X]) ^ (m + 1) * (1 - X) ^ (n + 1)) := by
  unfold belyiPush; push_cast; ring_nf

/-- The derivative of `X^m (1-X)^n`, for `m, n ≥ 1`. -/
