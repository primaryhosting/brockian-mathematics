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

def bellCoeff : Fin 4 → Fin 2 × Fin 2 → ℂ
  | 0, (0, 0) => 1
  | 0, (1, 1) => 1
  | 1, (0, 0) => 1
  | 1, (1, 1) => -1
  | 2, (0, 1) => 1
  | 2, (1, 0) => 1
  | 3, (0, 1) => 1
  | 3, (1, 0) => -1
  | _, _ => 0

/-- The four Bell states
`Φ⁺ = (|00⟩+|11⟩)/√2`, `Φ⁻ = (|00⟩-|11⟩)/√2`,
`Ψ⁺ = (|01⟩+|10⟩)/√2`, `Ψ⁻ = (|01⟩-|10⟩)/√2`. -/
