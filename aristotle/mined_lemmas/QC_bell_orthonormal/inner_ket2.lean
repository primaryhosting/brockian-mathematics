import Mathlib

/-!
# Bell Orthonormal
Category: Quantum Computing
Target: QC.bell_orthonormal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped TensorProduct

namespace QC

/-- A single qubit space `ℂ²`, with its Hermitian (Euclidean) inner product. -/
abbrev Qubit : Type := EuclideanSpace ℂ (Fin 2)

/-- The two-qubit space `ℂ² ⊗ ℂ²`. Mathlib's inner product on a tensor product of inner
product spaces is determined by `⟪a ⊗ b, c ⊗ d⟫ = ⟪a, c⟫ * ⟪b, d⟫`
(`TensorProduct.instInnerProductSpace`). -/
abbrev TwoQubit : Type := Qubit ⊗[ℂ] Qubit

/-- The computational basis kets `|0⟩`, `|1⟩` of a single qubit. -/

lemma inner_ket2 (i j k l : Fin 2) :
    inner ℂ (ket2 i j) (ket2 k l)
      = (if i = k then (1 : ℂ) else 0) * (if j = l then (1 : ℂ) else 0) := by
  simp [ket2, ket, TensorProduct.inner_tmul, EuclideanSpace.inner_single_left,
    EuclideanSpace.single_apply]

/-- The normalization constant `1/√2`. -/
