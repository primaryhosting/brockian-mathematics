import RequestProject.Schmidt

/-!
# Example: the Bell state

A concrete illustration of `QI.schmidt_decomposition`: the maximally entangled Bell state
on `ℂ^2 ⊗ ℂ^2` has Schmidt coefficients `1/√2, 1/√2`.
-/

open scoped BigOperators

namespace QI

/-- The Bell state `(|00⟩ + |11⟩)/√2` on `ℂ^2 ⊗ ℂ^2`. -/

def SchmidtDecomp.coeffs {psi : Fin m × Fin n → ℂ} (D : SchmidtDecomp psi) : Multiset ℝ :=
  Multiset.map D.lam Finset.univ.val

/-! ### Multisets of positive reals are determined by their power sums -/

