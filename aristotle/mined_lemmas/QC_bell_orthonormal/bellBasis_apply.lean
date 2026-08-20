import Mathlib

/-!
# Bell Orthonormal
Category: Quantum Computing
Target: QC.bell_orthonormal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
The four Bell states

  Φ⁺ = (|00⟩ + |11⟩)/√2,   Φ⁻ = (|00⟩ - |11⟩)/√2,
  Ψ⁺ = (|01⟩ + |10⟩)/√2,   Ψ⁻ = (|01⟩ - |10⟩)/√2

form an orthonormal basis of the two-qubit space ℂ² ⊗ ℂ².

The main statement `QC.bell_orthonormal` is formalised in the genuine tensor product
`EuclideanSpace ℂ (Fin 2) ⊗[ℂ] EuclideanSpace ℂ (Fin 2)`, carrying Mathlib's inner product
space structure on a tensor product of inner product spaces.  A second, coordinate version
on `EuclideanSpace ℂ (Fin 2 × Fin 2)` is given at the end of the file.
-/

namespace QC

open scoped TensorProduct ComplexConjugate

/-! ## The two-qubit space as a tensor product -/

/-- A single qubit: the Hilbert space `ℂ²`. -/
abbrev Qubit := EuclideanSpace ℂ (Fin 2)

/-- The computational basis vectors `|0⟩` and `|1⟩` of a single qubit. -/

@[simp] theorem bellBasis_apply (k : Fin 4) : bellBasis k = bell k := by
  simp [bellBasis]

/-! ## Coordinate version

The same statement, with `ℂ² ⊗ ℂ²` realised concretely as the space of functions
`Fin 2 × Fin 2 → ℂ` with the Euclidean inner product; the index `(i, j)` corresponds to the
computational basis vector `|i⟩ ⊗ |j⟩`. -/

/-- The two-qubit space in coordinates. -/
abbrev TwoQubit := EuclideanSpace ℂ (Fin 2 × Fin 2)

/-- Unnormalised coordinates of the four Bell states in the computational basis:
`|00⟩ + |11⟩`, `|00⟩ - |11⟩`, `|01⟩ + |10⟩`, `|01⟩ - |10⟩`. -/
