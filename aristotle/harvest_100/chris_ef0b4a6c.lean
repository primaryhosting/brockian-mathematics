import Mathlib

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

/-- A single qubit space `ℂ²`, as a two-dimensional complex inner product space. -/
abbrev Qubit : Type := EuclideanSpace ℂ (Fin 2)

/-- The two-qubit space `ℂ² ⊗ ℂ²`, with its canonical inner product
`⟪a ⊗ b, c ⊗ d⟫ = ⟪a, c⟫ * ⟪b, d⟫`. -/
abbrev TwoQubit : Type := Qubit ⊗[ℂ] Qubit

/-- The computational basis kets `|0⟩`, `|1⟩` of `ℂ²`. -/
noncomputable def ket (i : Fin 2) : Qubit := EuclideanSpace.single i (1 : ℂ)

lemma inner_ket (i j : Fin 2) :
    inner ℂ (ket i) (ket j) = (if i = j then (1 : ℂ) else 0) := by
  simp [ket, EuclideanSpace.inner_single_left, EuclideanSpace.single_apply]

/-- The four Bell states of `ℂ² ⊗ ℂ²`, in the order `Φ⁺, Φ⁻, Ψ⁺, Ψ⁻`. -/
noncomputable def bell : Fin 4 → TwoQubit
  | 0 => ((Real.sqrt 2 : ℂ))⁻¹ • (ket 0 ⊗ₜ[ℂ] ket 0 + ket 1 ⊗ₜ[ℂ] ket 1)
  | 1 => ((Real.sqrt 2 : ℂ))⁻¹ • (ket 0 ⊗ₜ[ℂ] ket 0 - ket 1 ⊗ₜ[ℂ] ket 1)
  | 2 => ((Real.sqrt 2 : ℂ))⁻¹ • (ket 0 ⊗ₜ[ℂ] ket 1 + ket 1 ⊗ₜ[ℂ] ket 0)
  | 3 => ((Real.sqrt 2 : ℂ))⁻¹ • (ket 0 ⊗ₜ[ℂ] ket 1 - ket 1 ⊗ₜ[ℂ] ket 0)

section InnerLemmas

/-! Restatements of the standard sesquilinearity lemmas for `TwoQubit`, stated with the
`Inner` instance that elaboration picks for `ℂ² ⊗ ℂ²`, so that they are usable by `rw`/`simp`. -/

lemma inner_smul_left' (c : ℂ) (x y : TwoQubit) :
    inner ℂ (c • x) y = (starRingEnd ℂ) c * inner ℂ x y := inner_smul_left x y c

lemma inner_smul_right' (c : ℂ) (x y : TwoQubit) :
    inner ℂ x (c • y) = c * inner ℂ x y := inner_smul_right x y c

lemma inner_add_left' (x y z : TwoQubit) :
    inner ℂ (x + y) z = inner ℂ x z + inner ℂ y z := inner_add_left x y z

lemma inner_add_right' (x y z : TwoQubit) :
    inner ℂ x (y + z) = inner ℂ x y + inner ℂ x z := inner_add_right x y z

lemma inner_sub_left' (x y z : TwoQubit) :
    inner ℂ (x - y) z = inner ℂ x z - inner ℂ y z := inner_sub_left x y z

lemma inner_sub_right' (x y z : TwoQubit) :
    inner ℂ x (y - z) = inner ℂ x y - inner ℂ x z := inner_sub_right x y z

end InnerLemmas

lemma inner_tmul_ket (a b c d : Fin 2) :
    inner ℂ (ket a ⊗ₜ[ℂ] ket b) (ket c ⊗ₜ[ℂ] ket d)
      = (if a = c then (1 : ℂ) else 0) * (if b = d then (1 : ℂ) else 0) := by
  rw [TensorProduct.inner_tmul, inner_ket, inner_ket]

lemma sqrt_two_inv_mul_self :
    ((Real.sqrt 2 : ℂ))⁻¹ * ((Real.sqrt 2 : ℂ))⁻¹ = (2 : ℂ)⁻¹ := by
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  norm_num

/-- The Bell states are pairwise orthogonal and of unit norm. -/
lemma inner_bell (i j : Fin 4) :
    inner ℂ (bell i) (bell j) = (if i = j then (1 : ℂ) else 0) := by
  fin_cases i <;> fin_cases j <;>
    simp only [bell, inner_smul_left', inner_smul_right', inner_add_left', inner_add_right',
      inner_sub_left', inner_sub_right', inner_tmul_ket] <;>
    norm_num <;>
    linear_combination (2 : ℂ) * sqrt_two_inv_mul_self

lemma bell_orthonormal_family : Orthonormal ℂ bell :=
  orthonormal_iff_ite.mpr fun i j => inner_bell i j

lemma finrank_twoQubit : Module.finrank ℂ TwoQubit = 4 := by
  rw [Module.finrank_tensorProduct, finrank_euclideanSpace_fin]

lemma card_fin_four_eq_finrank : Fintype.card (Fin 4) = Module.finrank ℂ TwoQubit := by
  rw [finrank_twoQubit, Fintype.card_fin]

/-- **The four Bell states form an orthonormal basis of `ℂ² ⊗ ℂ²`**: they are an orthonormal
family and their span is the whole space. -/
theorem bell_orthonormal :
    Orthonormal ℂ bell ∧ Submodule.span ℂ (Set.range bell) = ⊤ := by
  refine ⟨bell_orthonormal_family, ?_⟩
  have h := (basisOfOrthonormalOfCardEqFinrank bell_orthonormal_family
    card_fin_four_eq_finrank).span_eq
  rwa [coe_basisOfOrthonormalOfCardEqFinrank] at h

/-- The Bell states packaged as an `OrthonormalBasis` of `ℂ² ⊗ ℂ²`. -/
noncomputable def bellBasis : OrthonormalBasis (Fin 4) ℂ TwoQubit :=
  (basisOfOrthonormalOfCardEqFinrank bell_orthonormal_family
      card_fin_four_eq_finrank).toOrthonormalBasis
    (by rw [coe_basisOfOrthonormalOfCardEqFinrank]; exact bell_orthonormal_family)

@[simp] lemma bellBasis_apply (i : Fin 4) : bellBasis i = bell i := by
  simp [bellBasis, Module.Basis.coe_toOrthonormalBasis,
    coe_basisOfOrthonormalOfCardEqFinrank]

end QC

