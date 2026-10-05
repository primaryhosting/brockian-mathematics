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

lemma tqbasis_apply (p : Fin 2 × Fin 2) : tqbasis p = EuclideanSpace.single p (1 : ℂ) := by
  simp [tqbasis, EuclideanSpace.basisFun]
  rfl

/-- The canonical identification of the algebraic tensor product `ℂ² ⊗[ℂ] ℂ²` with the
coordinate model `TwoQubit`, sending `|i⟩ ⊗ |j⟩` to `|ij⟩`. -/
