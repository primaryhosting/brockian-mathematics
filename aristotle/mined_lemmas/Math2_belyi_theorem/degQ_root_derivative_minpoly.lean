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

lemma degQ_root_derivative_minpoly {α : ℂ} (h2 : 2 ≤ degQ α) {w : ℂ}
    (hw : aeval w (derivative (minpoly ℚ α)) = 0) : IsAlgebraic ℚ w ∧ degQ w ≤ degQ α - 1 := by
  have hne : derivative (minpoly ℚ α) ≠ 0 := by
    intro hcon
    have := Polynomial.natDegree_eq_zero_of_derivative_eq_zero hcon
    rw [degQ] at h2; omega
  refine ⟨⟨_, hne, hw⟩, ?_⟩
  have h1 := minpoly.degree_le_of_ne_zero ℚ w hne hw
  have h3 := Polynomial.natDegree_le_natDegree h1
  have h4 := Polynomial.natDegree_derivative_le (minpoly ℚ α)
  simp only [degQ] at *
  omega

/-- **Belyi reduction to `ℚ`**: a finite set of algebraic numbers can be mapped into `ℚ` by a
polynomial over `ℚ` all of whose critical values are also rational.  The induction is on the
maximal degree `D` occurring, and, for fixed `D`, on the number of points of degree `D`. -/
