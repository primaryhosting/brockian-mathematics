import RequestProject.Schmidt

/-!
# Example: the Bell state

A concrete illustration of `QI.schmidt_decomposition`: the maximally entangled Bell state
on `ℂ^2 ⊗ ℂ^2` has Schmidt coefficients `1/√2, 1/√2`.
-/

open scoped BigOperators

namespace QI

/-- The Bell state `(|00⟩ + |11⟩)/√2` on `ℂ^2 ⊗ ℂ^2`. -/

theorem bellState_coeffs (D : SchmidtDecomp bellState) :
    D.coeffs = {(Real.sqrt 2)⁻¹, (Real.sqrt 2)⁻¹} := by
  have h := (schmidt_decomposition bellState bellState_normalized).2 D bellSchmidt
  rw [h]
  rfl

end QI

import Mathlib

/-!
# The Schmidt decomposition of a bipartite pure state

A bipartite pure state on `ℂ^m ⊗ ℂ^n` is modelled as a normalized vector
`psi : Fin m × Fin n → ℂ`.  A *Schmidt decomposition* of `psi` consists of a rank `r`,
positive reals `lam k` (the Schmidt coefficients), and orthonormal families `e k` in `ℂ^m`
and `f k` in `ℂ^n` such that `psi (i, j) = ∑ k, lam k * e k i * f k j`.

The main result `QI.schmidt_decomposition` states that every bipartite pure state admits
such a decomposition, and that the multiset of Schmidt coefficients is uniquely determined.
-/

open scoped BigOperators ComplexOrder
open Matrix

namespace QI

variable {m n : ℕ}

/-- `v` is an orthonormal family of vectors in `ℂ^d`. -/
