import Mathlib

/-!
# Bell Orthonormal
Category: Quantum Computing
Target: QC.bell_orthonormal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QC

open scoped TensorProduct

/-- A single qubit space: `ℂ²` with its standard Hermitian inner product. -/
abbrev Qubit : Type := EuclideanSpace ℂ (Fin 2)

/-- The two-qubit space `ℂ² ⊗ ℂ²`. Mathlib equips a tensor product of inner product spaces
with the inner product determined by `⟪a ⊗ b, c ⊗ d⟫ = ⟪a, c⟫ * ⟪b, d⟫`. -/
abbrev TwoQubit : Type := Qubit ⊗[ℂ] Qubit

/-- The computational basis vectors `|0⟩`, `|1⟩` of a single qubit. -/
noncomputable def ket (i : Fin 2) : Qubit := EuclideanSpace.single i 1

lemma inner_ket (i j : Fin 2) :
    inner ℂ (ket i) (ket j) = if i = j then (1 : ℂ) else 0 := by
  simp [ket, EuclideanSpace.inner_single_left, EuclideanSpace.single_apply]

lemma norm_ket (i : Fin 2) : ‖ket i‖ = 1 := by
  simp [ket, EuclideanSpace.norm_single]

/-- The unnormalized Bell vectors `|00⟩ ± |11⟩` and `|01⟩ ± |10⟩`. -/
noncomputable def bellRaw : Fin 4 → TwoQubit :=
  ![ ket 0 ⊗ₜ[ℂ] ket 0 + ket 1 ⊗ₜ[ℂ] ket 1,
     ket 0 ⊗ₜ[ℂ] ket 0 - ket 1 ⊗ₜ[ℂ] ket 1,
     ket 0 ⊗ₜ[ℂ] ket 1 + ket 1 ⊗ₜ[ℂ] ket 0,
     ket 0 ⊗ₜ[ℂ] ket 1 - ket 1 ⊗ₜ[ℂ] ket 0 ]

/-- The unnormalized Bell vectors are pairwise orthogonal, each of squared norm `2`. -/
lemma inner_bellRaw (i j : Fin 4) :
    inner ℂ (bellRaw i) (bellRaw j) = if i = j then (2 : ℂ) else 0 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [bellRaw, inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
      TensorProduct.inner_tmul, inner_ket, norm_ket]

/-- The normalization constant `1/√2`. -/
noncomputable def invSqrt2 : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)⁻¹

lemma invSqrt2_mul_self : invSqrt2 * invSqrt2 = 1 / 2 := by
  have h : (Real.sqrt 2 : ℝ) * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, h]; norm_num
  rw [invSqrt2, ← mul_inv, h2]
  norm_num

lemma conj_invSqrt2 : (starRingEnd ℂ) invSqrt2 = invSqrt2 := by
  simp [invSqrt2, ← Complex.ofReal_inv]

/-- The four Bell states
`Φ⁺ = (|00⟩+|11⟩)/√2`, `Φ⁻ = (|00⟩-|11⟩)/√2`,
`Ψ⁺ = (|01⟩+|10⟩)/√2`, `Ψ⁻ = (|01⟩-|10⟩)/√2`. -/
noncomputable def bell (k : Fin 4) : TwoQubit := invSqrt2 • bellRaw k

/-- Sesquilinearity of the inner product on `TwoQubit`, restated so that the scalar action
matches the one used in `QC.bell`. -/
lemma inner_smul_left_twoQubit (x y : TwoQubit) (r : ℂ) :
    inner ℂ (r • x) y = (starRingEnd ℂ) r * inner ℂ x y :=
  inner_smul_left x y r

lemma inner_smul_right_twoQubit (x y : TwoQubit) (r : ℂ) :
    inner ℂ x (r • y) = r * inner ℂ x y :=
  inner_smul_right x y r

/-- The Bell states are pairwise orthogonal unit vectors. -/
lemma inner_bell (i j : Fin 4) :
    inner ℂ (bell i) (bell j) = if i = j then (1 : ℂ) else 0 := by
  rw [bell, bell, inner_smul_left_twoQubit, inner_smul_right_twoQubit, conj_invSqrt2,
    inner_bellRaw, ← mul_assoc, invSqrt2_mul_self]
  split <;> norm_num

lemma bell_orthonormal_family : Orthonormal ℂ bell :=
  (orthonormal_iff_ite).2 inner_bell

lemma finrank_twoQubit : Module.finrank ℂ TwoQubit = 4 := by
  simp [Module.finrank_tensorProduct]

/-- The Bell states, packaged as a basis of `ℂ² ⊗ ℂ²`. -/
noncomputable def bellBasisAux : Module.Basis (Fin 4) ℂ TwoQubit :=
  basisOfLinearIndependentOfCardEqFinrank bell_orthonormal_family.linearIndependent
    (by rw [Fintype.card_fin, finrank_twoQubit])

lemma coe_bellBasisAux : (bellBasisAux : Fin 4 → TwoQubit) = bell :=
  coe_basisOfLinearIndependentOfCardEqFinrank _ _

/-- The Bell states, packaged as an orthonormal basis of `ℂ² ⊗ ℂ²`. -/
noncomputable def bellBasis : OrthonormalBasis (Fin 4) ℂ TwoQubit :=
  bellBasisAux.toOrthonormalBasis (by rw [coe_bellBasisAux]; exact bell_orthonormal_family)

@[simp] lemma coe_bellBasis : (bellBasis : Fin 4 → TwoQubit) = bell := by
  rw [bellBasis, Module.Basis.coe_toOrthonormalBasis, coe_bellBasisAux]

/-- **The four Bell states form an orthonormal basis of `ℂ² ⊗ ℂ²`**: they are pairwise
orthogonal unit vectors and they span the whole space. -/
theorem bell_orthonormal :
    Orthonormal ℂ bell ∧ Submodule.span ℂ (Set.range bell) = ⊤ := by
  refine ⟨bell_orthonormal_family, ?_⟩
  rw [← coe_bellBasisAux]
  exact bellBasisAux.span_eq

end QC

