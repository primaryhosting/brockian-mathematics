import RequestProject.Schmidt

/-!
# Example: the Bell state

A concrete illustration of `QI.schmidt_decomposition`: the maximally entangled Bell state
on `ℂ^2 ⊗ ℂ^2` has Schmidt coefficients `1/√2, 1/√2`.
-/

open scoped BigOperators

namespace QI

/-- The Bell state `(|00⟩ + |11⟩)/√2` on `ℂ^2 ⊗ ℂ^2`. -/

lemma rho_mulVec_eigVec (k i : Fin m) :
    ∑ i', rho psi i i' * eigVec psi k i' = (eigMu psi k : ℂ) * eigVec psi k i := by
  have h := (rho_posSemidef psi).isHermitian.mulVec_eigenvectorBasis k
  have := congrFun h i
  simpa [Matrix.mulVec, dotProduct, eigVec, eigMu, Complex.real_smul, mul_comm] using this

/-- The (unnormalized) vectors on the second factor. -/
