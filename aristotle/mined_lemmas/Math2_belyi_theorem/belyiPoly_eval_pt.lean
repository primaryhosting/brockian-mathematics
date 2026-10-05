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

lemma belyiPoly_eval_pt (a b : ℕ) : (belyiPoly a b).eval (belyiPt a b) = 1 := by
  rw [belyiPoly_eval]
  unfold belyiC
  have h1 := belyiPt_pos a b
  have h2 := one_sub_belyiPt_pos a b
  field_simp

