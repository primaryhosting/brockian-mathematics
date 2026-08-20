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

lemma inner_combo (a b c d a' b' c' d' : Fin 2) (s t : ℂ) :
    inner ℂ (combo a b c d s) (combo a' b' c' d' t)
      = (1 / 2 : ℂ) * ((if a = a' then 1 else 0) * (if b = b' then 1 else 0)
        + t * ((if a = c' then 1 else 0) * (if b = d' then 1 else 0))
        + (starRingEnd ℂ) s * ((if c = a' then 1 else 0) * (if d = b' then 1 else 0))
        + (starRingEnd ℂ) s * t * ((if c = c' then 1 else 0) * (if d = d' then 1 else 0))) := by
  simp only [combo, tp_inner_smul_left, tp_inner_smul_right, tp_inner_add_left,
    tp_inner_add_right, inner_ket2, conj_invSqrt2]
  linear_combination ((if a = a' then (1 : ℂ) else 0) * (if b = b' then 1 else 0)
    + t * ((if a = c' then 1 else 0) * (if b = d' then 1 else 0))
    + (starRingEnd ℂ) s * ((if c = a' then 1 else 0) * (if d = b' then 1 else 0))
    + (starRingEnd ℂ) s * t * ((if c = c' then 1 else 0) * (if d = d' then 1 else 0)))
      * invSqrt2_mul_self

/-- The four Bell states
`Φ⁺ = (|00⟩ + |11⟩)/√2`, `Φ⁻ = (|00⟩ - |11⟩)/√2`,
`Ψ⁺ = (|01⟩ + |10⟩)/√2`, `Ψ⁻ = (|01⟩ - |10⟩)/√2`. -/
