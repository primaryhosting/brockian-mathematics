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

/-- The state space of two qubits, `ℂ² ⊗ ℂ²`, modelled as the Hilbert space
`EuclideanSpace ℂ (Fin 2 × Fin 2)`: functions on pairs of bits with the standard
Hermitian inner product.  The basis vector indexed by `(a, b)` is the product state
`|a⟩ ⊗ |b⟩`. -/
abbrev TwoQubit := EuclideanSpace ℂ (Fin 2 × Fin 2)

/-- The product state `|a⟩ ⊗ |b⟩` of two qubit basis states. -/

theorem bell_eq :
    bell 0 = (Real.sqrt 2 : ℂ)⁻¹ • (ket 0 0 + ket 1 1) ∧
    bell 1 = (Real.sqrt 2 : ℂ)⁻¹ • (ket 0 0 - ket 1 1) ∧
    bell 2 = (Real.sqrt 2 : ℂ)⁻¹ • (ket 0 1 + ket 1 0) ∧
    bell 3 = (Real.sqrt 2 : ℂ)⁻¹ • (ket 0 1 - ket 1 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · ext p
    obtain ⟨a, b⟩ := p
    fin_cases a <;> fin_cases b <;>
      simp [bell, bellCoeff, ket, EuclideanSpace.single_apply, Prod.ext_iff]

/-- The inner product on the two-qubit space, expanded over the computational basis. -/
