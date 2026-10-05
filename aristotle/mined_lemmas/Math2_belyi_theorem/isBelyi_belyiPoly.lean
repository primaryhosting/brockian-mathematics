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

lemma isBelyi_belyiPoly (a b : ℕ) : IsBelyi (belyiPoly a b) :=
  ⟨belyiPoly_natDegree_pos a b, critVal_belyiPoly a b⟩

/-! ## The theorem -/

/-- A choice of rational representative of a rational complex number. -/
