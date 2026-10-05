/-
# Bell Orthonormal
Category: Quantum Computing
Target: QC.bell_orthonormal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Bell Orthonormal
Category: Quantum Computing
Target: QC.bell_orthonormal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

open scoped ComplexConjugate TensorProduct

/-- The two-qubit state space `ℂ² ⊗ ℂ²`, realized as the Hilbert space of functions on the
product index set `Fin 2 × Fin 2` (the computational basis `|ij⟩`).  The identification with
the algebraic tensor product `ℂ² ⊗[ℂ] ℂ²` is given by `QC.tensorEquiv` below. -/
abbrev TwoQubit := EuclideanSpace ℂ (Fin 2 × Fin 2)

/-- Coordinates of the four Bell states in the computational basis, before normalization. -/

noncomputable def tqbasis : Module.Basis (Fin 2 × Fin 2) ℂ TwoQubit :=
  (EuclideanSpace.basisFun (Fin 2 × Fin 2) ℂ).toBasis

