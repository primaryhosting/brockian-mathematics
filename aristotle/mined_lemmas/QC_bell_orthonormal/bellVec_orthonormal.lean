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

theorem bellVec_orthonormal :
    Orthonormal ℂ bellVec ∧ Submodule.span ℂ (Set.range bellVec) = ⊤ := by
  refine ⟨bellVec_orthonormal_family, ?_⟩
  have hcard : Fintype.card (Fin 4) = Module.finrank ℂ TwoQubit := by
    simp [finrank_euclideanSpace]
  have := (basisOfOrthonormalOfCardEqFinrank bellVec_orthonormal_family hcard).span_eq
  rwa [coe_basisOfOrthonormalOfCardEqFinrank] at this

/-- The coordinate Bell states packaged as an `OrthonormalBasis`. -/
