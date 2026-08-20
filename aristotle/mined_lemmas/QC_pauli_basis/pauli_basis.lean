import Mathlib

/-!
# Pauli Basis
Category: Quantum Computing
Target: QC.pauli_basis
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

open Matrix

/-- The identity Pauli matrix `I`. -/

theorem pauli_basis :
    LinearIndependent ℂ pauli ∧ Submodule.span ℂ (Set.range pauli) = ⊤ :=
  ⟨pauli_linearIndependent, pauli_span⟩

/-- The basis of `Matrix (Fin 2) (Fin 2) ℂ` given by the Pauli matrices. -/
