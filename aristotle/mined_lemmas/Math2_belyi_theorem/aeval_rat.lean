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

theorem aeval_rat (p : ℚ[X]) (q : ℚ) : aeval ((q : ℂ)) p = ((p.eval q : ℚ) : ℂ) := by
  have h : ((q : ℂ)) = algebraMap ℚ ℂ q := by simp
  rw [h, aeval_algebraMap_apply]; simp

/-- The normalized Belyi polynomial `((m+n)^(m+n) / (m^m n^n)) * X^m * (1-X)^n`. -/
