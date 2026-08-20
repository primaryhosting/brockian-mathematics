import RequestProject.Schmidt

/-!
# Example: the Bell state

A concrete illustration of `QI.schmidt_decomposition`: the maximally entangled Bell state
on `ℂ^2 ⊗ ℂ^2` has Schmidt coefficients `1/√2, 1/√2`.
-/

open scoped BigOperators

namespace QI

/-- The Bell state `(|00⟩ + |11⟩)/√2` on `ℂ^2 ⊗ ℂ^2`. -/

lemma eigVec_orthonormal (k l : Fin m) :
    ∑ i, (starRingEnd ℂ) (eigVec psi k i) * eigVec psi l i = if k = l then 1 else 0 := by
  have h := Matrix.UnitaryGroup.star_mul_self
    (rho_posSemidef psi).isHermitian.eigenvectorUnitary
  have := congrFun (congrFun h k) l
  simpa [Matrix.mul_apply, Matrix.one_apply, eigVec] using this

