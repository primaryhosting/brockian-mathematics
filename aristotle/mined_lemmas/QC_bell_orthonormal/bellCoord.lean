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

noncomputable def bellCoord : Fin 4 → (Fin 2 × Fin 2) → ℂ := fun i p =>
  match i, p with
  | 0, (0, 0) => invSqrt2
  | 0, (1, 1) => invSqrt2
  | 1, (0, 0) => invSqrt2
  | 1, (1, 1) => -invSqrt2
  | 2, (0, 1) => invSqrt2
  | 2, (1, 0) => invSqrt2
  | 3, (0, 1) => invSqrt2
  | 3, (1, 0) => -invSqrt2
  | _, _ => 0

/-- The four Bell states, as vectors of the two-qubit space. -/
