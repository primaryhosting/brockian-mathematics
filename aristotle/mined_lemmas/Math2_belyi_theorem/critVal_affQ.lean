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

lemma critVal_affQ (a b : ℚ) (h : a ≠ b) : critVal (affQ a b) = ∅ := by
  refine critVal_eq_empty_of_derivative_const _ ((b - a)⁻¹) ?_ (derivative_affQ a b)
  simp only [ne_eq, inv_eq_zero, sub_eq_zero]
  exact fun hh => h hh.symm

