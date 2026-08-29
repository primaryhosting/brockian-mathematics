/-!
# Bell Orthonormal
Category: Quantum Computing
Target: QC.bell_orthonormal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped ComplexConjugate

namespace QC

/-- The state space of two qubits, `ℂ² ⊗ ℂ²`, realized concretely as the
finite-dimensional Hilbert space `EuclideanSpace ℂ (Fin 2 × Fin 2)`, whose standard basis
is the computational basis `|00⟩, |01⟩, |10⟩, |11⟩`. -/
abbrev TwoQubit := EuclideanSpace ℂ (Fin 2 × Fin 2)

/-- The normalization constant `1/√2`. -/

lemma coe_bellLinearBasis : ⇑bellLinearBasis = bell :=
  coe_basisOfLinearIndependentOfCardEqFinrank _ _

/-- The four Bell states, packaged as an orthonormal basis of the two-qubit space
`ℂ² ⊗ ℂ² ≅ EuclideanSpace ℂ (Fin 2 × Fin 2)`. -/
