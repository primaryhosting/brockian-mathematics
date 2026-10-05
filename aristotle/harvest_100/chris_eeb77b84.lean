/-!
# Bell Orthonormal
Category: Quantum Computing
Target: QC.bell_orthonormal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped TensorProduct

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QC

/-- A single qubit space: `ℂ²` with its standard (Euclidean) inner product. -/
abbrev Qubit : Type := EuclideanSpace ℂ (Fin 2)

/-- The two-qubit space `ℂ² ⊗ ℂ²`, with the tensor-product inner product. -/
abbrev TwoQubit : Type := Qubit ⊗[ℂ] Qubit

/-- The computational basis kets `|0⟩` and `|1⟩` of a single qubit. -/
noncomputable def ket (i : Fin 2) : Qubit := EuclideanSpace.single i 1

/-- The normalization constant `1 / √2`. -/
noncomputable def invSqrt2 : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)⁻¹

lemma conj_invSqrt2 : (starRingEnd ℂ) invSqrt2 = invSqrt2 := by
  rw [invSqrt2, map_inv₀, Complex.conj_ofReal]

lemma invSqrt2_mul_self : invSqrt2 * invSqrt2 = 1 / 2 := by
  have h : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
    norm_num
  rw [invSqrt2, ← mul_inv, h]
  norm_num

lemma invSqrt2_sq_two : invSqrt2 ^ 2 * 2 = 1 := by
  rw [pow_two, invSqrt2_mul_self]
  norm_num

/-- The computational basis of `ℂ² ⊗ ℂ²` is orthonormal. -/
lemma inner_ket_tmul_ket (a b c d : Fin 2) :
    inner ℂ (ket a ⊗ₜ[ℂ] ket b) (ket c ⊗ₜ[ℂ] ket d)
      = (if a = c then 1 else 0) * (if b = d then 1 else 0) := by
  rw [TensorProduct.inner_tmul]
  simp [ket, EuclideanSpace.inner_single_left, EuclideanSpace.single_apply]

/- Scalar multiplication on `ℂ² ⊗ ℂ²` reaches the inner product through a different
(definitionally equal) instance path, so we restate the two `inner`/`smul` lemmas here. -/
lemma inner_smul_l (x y : TwoQubit) (c : ℂ) :
    inner ℂ (c • x) y = (starRingEnd ℂ) c * inner ℂ x y := inner_smul_left x y c

lemma inner_smul_r (x y : TwoQubit) (c : ℂ) :
    inner ℂ x (c • y) = c * inner ℂ x y := inner_smul_right x y c

/-- The four Bell states
`Φ⁺ = (|00⟩+|11⟩)/√2`, `Φ⁻ = (|00⟩-|11⟩)/√2`,
`Ψ⁺ = (|01⟩+|10⟩)/√2`, `Ψ⁻ = (|01⟩-|10⟩)/√2`. -/
noncomputable def bell : Fin 4 → TwoQubit
  | 0 => invSqrt2 • (ket 0 ⊗ₜ ket 0 + ket 1 ⊗ₜ ket 1)
  | 1 => invSqrt2 • (ket 0 ⊗ₜ ket 0 - ket 1 ⊗ₜ ket 1)
  | 2 => invSqrt2 • (ket 0 ⊗ₜ ket 1 + ket 1 ⊗ₜ ket 0)
  | 3 => invSqrt2 • (ket 0 ⊗ₜ ket 1 - ket 1 ⊗ₜ ket 0)

lemma finrank_twoQubit : Module.finrank ℂ TwoQubit = 4 := by
  rw [Module.finrank_tensorProduct, finrank_euclideanSpace_fin]

lemma bell_orthonormal_family : Orthonormal ℂ bell := by
  rw [orthonormal_iff_ite]
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp only [bell, inner_smul_l, inner_smul_r, inner_add_left, inner_add_right,
      inner_sub_left, inner_sub_right, inner_ket_tmul_ket, conj_invSqrt2] <;>
    norm_num <;>
    ring_nf <;>
    exact invSqrt2_sq_two

lemma bell_span_top : Submodule.span ℂ (Set.range bell) = ⊤ :=
  bell_orthonormal_family.linearIndependent.span_eq_top_of_card_eq_finrank
    (by rw [finrank_twoQubit]; simp)

/-- **The four Bell states form an orthonormal basis of `ℂ² ⊗ ℂ²`**: they are an
orthonormal family and they span the whole space. -/
theorem bell_orthonormal :
    Orthonormal ℂ bell ∧ Submodule.span ℂ (Set.range bell) = ⊤ :=
  ⟨bell_orthonormal_family, bell_span_top⟩

/-- The Bell states packaged as an orthonormal basis of `ℂ² ⊗ ℂ²`. -/
noncomputable def bellBasis : OrthonormalBasis (Fin 4) ℂ TwoQubit :=
  OrthonormalBasis.mk bell_orthonormal_family (by rw [bell_span_top])

@[simp] lemma bellBasis_apply (i : Fin 4) : bellBasis i = bell i :=
  OrthonormalBasis.coe_mk _ _ ▸ rfl

end QC

