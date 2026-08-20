import RequestProject.Schmidt

/-!
# Example: the Bell state

A concrete illustration of `QI.schmidt_decomposition`: the maximally entangled Bell state
on `ℂ^2 ⊗ ℂ^2` has Schmidt coefficients `1/√2, 1/√2`.
-/

open scoped BigOperators

namespace QI

/-- The Bell state `(|00⟩ + |11⟩)/√2` on `ℂ^2 ⊗ ℂ^2`. -/

lemma trace_rho (psi : Fin m × Fin n → ℂ) :
    (rho psi).trace = ((∑ x, ‖psi x‖ ^ 2 : ℝ) : ℂ) := by
  simp [Matrix.trace, Matrix.diag, rho, Fintype.sum_prod_type, Complex.mul_conj,
    Complex.normSq_eq_norm_sq]

