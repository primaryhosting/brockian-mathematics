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

@[simp] lemma coe_pauliBasis : ⇑pauliBasis = pauli := Module.Basis.coe_mk _ _

/-- Explicit expansion of an arbitrary 2×2 complex matrix in the Pauli basis. -/
