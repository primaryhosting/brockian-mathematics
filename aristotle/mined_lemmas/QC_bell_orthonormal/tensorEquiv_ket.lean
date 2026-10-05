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

@[simp] lemma tensorEquiv_ket (i j : Fin 2) :
    tensorEquiv (ket i ⊗ₜ ket j) = EuclideanSpace.single (i, j) (1 : ℂ) := by
  rw [← qbasis_apply i, ← qbasis_apply j, ← tqbasis_apply (i, j),
    ← Module.Basis.tensorProduct_apply, tensorEquiv, Module.Basis.equiv_apply, Equiv.refl_apply]

