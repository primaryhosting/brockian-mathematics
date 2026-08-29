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

noncomputable def bellLinearBasis : Module.Basis (Fin 4) ℂ TwoQubit :=
  basisOfLinearIndependentOfCardEqFinrank bell_orthonormal_family.linearIndependent
    (by simp)

