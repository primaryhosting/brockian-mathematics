import Mathlib

/-!
# No Cloning
Category: Quantum Computing
Target: QC.no_cloning
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


open scoped ComplexConjugate InnerProductSpace

namespace QC

/-- The state space of one qubit, `ℂ²` with the Euclidean (Hilbert) structure. -/
noncomputable abbrev Qubit := EuclideanSpace ℂ (Fin 2)

/-- The state space of two qubits, i.e. `Qubit ⊗ Qubit` realized concretely as
functions on `Fin 2 × Fin 2`. -/
noncomputable abbrev Qubit2 := EuclideanSpace ℂ (Fin 2 × Fin 2)

/-- The tensor product of two qubit states. -/

noncomputable def qplus : Qubit := !₂[(Real.sqrt 2)⁻¹, (Real.sqrt 2)⁻¹]

