import Mathlib
/-!
# Belyi Theorem
Category: Frontier Math
Target: Math2.belyi_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Classical

set_option maxHeartbeats 1000000

namespace Math2

open Polynomial IntermediateField

noncomputable section

/-! ## Basic notions -/

/-- The set of critical values in `ℂ` of a polynomial with rational coefficients.
Viewing `f ∈ ℚ[X]` as a morphism `ℙ¹ → ℙ¹`, these are the finite branch points of `f`. -/

lemma critVal_X : critVal (X : ℚ[X]) = ∅ :=
  critVal_eq_empty_of_derivative_const X 1 one_ne_zero (by simp)

/-! ## The Belyi polynomials

For `a b : ℕ` the polynomial `belyiPoly a b = c ⬝ x^(a+1) (1-x)^(b+1)` has all its critical
values in `{0, 1}`, and it sends the rational point `belyiPt a b = (a+1)/(a+b+2)` to `1`. -/

/-- The distinguished critical point `(a+1)/(a+b+2) ∈ (0,1)`. -/
