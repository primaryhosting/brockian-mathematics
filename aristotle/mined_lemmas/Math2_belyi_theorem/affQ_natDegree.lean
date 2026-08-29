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

lemma affQ_natDegree (a b : ℚ) (h : a ≠ b) : (affQ a b).natDegree = 1 := by
  have hba : (b - a)⁻¹ ≠ 0 := by
    simp only [ne_eq, inv_eq_zero, sub_eq_zero]
    exact fun hh => h hh.symm
  unfold affQ
  rw [Polynomial.natDegree_C_mul hba]
  compute_degree!

