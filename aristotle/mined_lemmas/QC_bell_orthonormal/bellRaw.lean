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

def bellRaw : Fin 4 → Fin 2 × Fin 2 → ℂ
  | 0, p => if p = (0, 0) then 1 else if p = (1, 1) then 1 else 0
  | 1, p => if p = (0, 0) then 1 else if p = (1, 1) then -1 else 0
  | 2, p => if p = (0, 1) then 1 else if p = (1, 0) then 1 else 0
  | 3, p => if p = (0, 1) then 1 else if p = (1, 0) then -1 else 0

/-- The four Bell states in coordinates, each normalised by `1/√2`. -/
