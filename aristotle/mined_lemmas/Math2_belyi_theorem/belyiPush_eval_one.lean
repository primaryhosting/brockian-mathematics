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

theorem belyiPush_eval_one (m n : ℕ) : (belyiPush (m + 1) (n + 1)).eval 1 = 0 := by
  rw [belyiPush_eq]; simp

/-- `belyiPush (m+1) (n+1)` sends `(m+1)/(m+n+2)` to `1`. -/
