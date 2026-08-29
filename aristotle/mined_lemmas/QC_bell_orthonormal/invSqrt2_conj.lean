/-
# Bell Orthonormal
Category: Quantum Computing
Target: QC.bell_orthonormal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QC

open scoped ComplexConjugate

/-- The two–qubit state space `ℂ² ⊗ ℂ²`, modelled as the Hilbert space of functions
`Fin 2 × Fin 2 → ℂ` (the computational basis `|ij⟩` is indexed by pairs `(i, j)`). -/
abbrev Qubit2 := EuclideanSpace ℂ (Fin 2 × Fin 2)

/-- The normalisation constant `1/√2`. -/

lemma invSqrt2_conj : conj invSqrt2 = invSqrt2 := by
  simp [invSqrt2, ← Complex.ofReal_inv, Complex.conj_ofReal]

