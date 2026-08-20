import Mathlib

/-!
# Bell Orthonormal
Category: Quantum Computing
Target: QC.bell_orthonormal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

open scoped ComplexConjugate

/-- The two-qubit state space `ℂ² ⊗ ℂ²`, realised concretely as the Hilbert space
of functions `Fin 2 × Fin 2 → ℂ` with the standard inner product. -/
abbrev TwoQubit := EuclideanSpace ℂ (Fin 2 × Fin 2)

/-- Unnormalised coefficients of the four Bell states in the computational basis
`|00⟩, |01⟩, |10⟩, |11⟩`. -/

private lemma card_eq_finrank : Fintype.card (Fin 4) = Module.finrank ℂ TwoQubit := by
  rw [finrank_twoQubit, Fintype.card_fin]

/-- The Bell states, packaged as an orthonormal basis of `ℂ² ⊗ ℂ²`. -/
