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

theorem bell_orthonormal_aux : Orthonormal ℂ bell := by
  rw [orthonormal_iff_ite]
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp only [bell, Fin.reduceFinMk, Matrix.cons_val] <;>
    rw [inner_combo] <;> norm_num <;> decide

