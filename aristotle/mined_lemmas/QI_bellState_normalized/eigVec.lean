import RequestProject.Schmidt

/-!
# Example: the Bell state

A concrete illustration of `QI.schmidt_decomposition`: the maximally entangled Bell state
on `ℂ^2 ⊗ ℂ^2` has Schmidt coefficients `1/√2, 1/√2`.
-/

open scoped BigOperators

namespace QI

/-- The Bell state `(|00⟩ + |11⟩)/√2` on `ℂ^2 ⊗ ℂ^2`. -/

noncomputable def eigVec (k : Fin m) : Fin m → ℂ := fun i =>
  ((rho_posSemidef psi).isHermitian.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ) i k

