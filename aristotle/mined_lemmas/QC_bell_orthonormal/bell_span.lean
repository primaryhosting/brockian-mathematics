/-
# Bell Orthonormal
Category: Quantum Computing
Target: QC.bell_orthonormal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QC

open scoped ComplexConjugate

/-- The two–qubit state space `ℂ² ⊗ ℂ²`, modelled as the Hilbert space of functions
`Fin 2 × Fin 2 → ℂ` (the computational basis `|ij⟩` is indexed by pairs `(i, j)`). -/
abbrev Qubit2 := EuclideanSpace ℂ (Fin 2 × Fin 2)

/-- The normalisation constant `1/√2`. -/

theorem bell_span : Submodule.span ℂ (Set.range bell) = ⊤ := by
  rw [← coe_basisOfOrthonormalOfCardEqFinrank bell_orthonormal_family card_eq_finrank]
  exact Module.Basis.span_eq _

/-- **The four Bell states form an orthonormal basis of `ℂ² ⊗ ℂ²`**: they are pairwise
orthogonal unit vectors and they span the whole space. -/
