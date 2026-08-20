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

lemma invSqrt2_mul_self : invSqrt2 * invSqrt2 = 1 / 2 := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have h : ((Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ : ℝ) = 1 / 2 := by
    field_simp
    linarith [h2]
  simp only [invSqrt2, ← Complex.ofReal_mul, h]
  norm_num

