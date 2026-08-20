import RequestProject.Schmidt

/-!
# Example: the Bell state

A concrete illustration of `QI.schmidt_decomposition`: the maximally entangled Bell state
on `ℂ^2 ⊗ ℂ^2` has Schmidt coefficients `1/√2, 1/√2`.
-/

open scoped BigOperators

namespace QI

/-- The Bell state `(|00⟩ + |11⟩)/√2` on `ℂ^2 ⊗ ℂ^2`. -/

lemma rho_posSemidef (psi : Fin m × Fin n → ℂ) : (rho psi).PosSemidef := by
  rw [rho_eq_mul_conjTranspose]
  exact Matrix.posSemidef_self_mul_conjTranspose _

