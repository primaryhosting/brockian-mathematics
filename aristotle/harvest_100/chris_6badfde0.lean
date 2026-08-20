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
noncomputable def ket (i : Fin 2) : Qubit := EuclideanSpace.single i 1

/-- The computational basis of a qubit is orthonormal. -/
lemma inner_ket (i j : Fin 2) : inner ℂ (ket i) (ket j) = if i = j then (1 : ℂ) else 0 := by
  simp [ket, EuclideanSpace.inner_single_right]
  aesop

/-- Inner products of the four product states `|ab⟩ = |a⟩ ⊗ |b⟩`. -/
lemma inner_ket_tmul (a b c d : Fin 2) :
    inner ℂ (ket a ⊗ₜ[ℂ] ket b) (ket c ⊗ₜ[ℂ] ket d) = if a = c ∧ b = d then (1 : ℂ) else 0 := by
  rw [TensorProduct.inner_tmul, inner_ket, inner_ket]
  aesop

/- The two lemmas below are instances of `inner_smul_left`/`inner_smul_right`, restated with the
scalar action coming from the tensor product's own module structure so that they are usable as
rewrite rules. -/

private lemma tp_inner_smul_left (r : ℂ) (x y : Qubit ⊗[ℂ] Qubit) :
    inner ℂ (r • x) y = conj r * inner ℂ x y := inner_smul_left x y r

private lemma tp_inner_smul_right (r : ℂ) (x y : Qubit ⊗[ℂ] Qubit) :
    inner ℂ x (r • y) = r * inner ℂ x y := inner_smul_right x y r

/-- The four Bell states `Φ⁺, Φ⁻, Ψ⁺, Ψ⁻` in `ℂ² ⊗ ℂ²`. -/
noncomputable def bell : Fin 4 → Qubit ⊗[ℂ] Qubit
  | 0 => ((Real.sqrt 2 : ℂ))⁻¹ • (ket 0 ⊗ₜ[ℂ] ket 0 + ket 1 ⊗ₜ[ℂ] ket 1)
  | 1 => ((Real.sqrt 2 : ℂ))⁻¹ • (ket 0 ⊗ₜ[ℂ] ket 0 - ket 1 ⊗ₜ[ℂ] ket 1)
  | 2 => ((Real.sqrt 2 : ℂ))⁻¹ • (ket 0 ⊗ₜ[ℂ] ket 1 + ket 1 ⊗ₜ[ℂ] ket 0)
  | 3 => ((Real.sqrt 2 : ℂ))⁻¹ • (ket 0 ⊗ₜ[ℂ] ket 1 - ket 1 ⊗ₜ[ℂ] ket 0)

/-- The Bell states are pairwise orthogonal and of unit norm. -/
lemma inner_bell (i j : Fin 4) : inner ℂ (bell i) (bell j) = if i = j then (1 : ℂ) else 0 := by
  have h2 : ((Real.sqrt 2 : ℂ))⁻¹ * ((Real.sqrt 2 : ℂ))⁻¹ = 2⁻¹ := by
    rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, ← Real.sqrt_inv,
      ← Real.sqrt_mul (by positivity)]
    norm_num
  fin_cases i <;> fin_cases j <;>
    simp only [bell, tp_inner_smul_left, tp_inner_smul_right, inner_add_left, inner_add_right,
      inner_sub_left, inner_sub_right, inner_ket_tmul, ← Complex.ofReal_inv,
      Complex.conj_ofReal] <;>
    norm_num <;>
    linear_combination (2 : ℂ) * h2

/-- The four Bell states form an orthonormal family in `ℂ² ⊗ ℂ²`. -/
theorem bell_orthonormal_family : Orthonormal ℂ bell :=
  orthonormal_iff_ite.2 inner_bell

/-- **The four Bell states form an orthonormal basis of `ℂ² ⊗ ℂ²`**: they are an orthonormal
family, and they span the whole space. -/
theorem bell_orthonormal :
    Orthonormal ℂ bell ∧ Submodule.span ℂ (Set.range bell) = ⊤ := by
  refine ⟨bell_orthonormal_family, ?_⟩
  have hcard : Fintype.card (Fin 4) = Module.finrank ℂ (Qubit ⊗[ℂ] Qubit) := by
    simp [Module.finrank_tensorProduct, finrank_euclideanSpace]
  have := (basisOfOrthonormalOfCardEqFinrank bell_orthonormal_family hcard).span_eq
  rwa [coe_basisOfOrthonormalOfCardEqFinrank] at this

/-- The Bell states packaged as an `OrthonormalBasis` of `ℂ² ⊗ ℂ²`. -/
noncomputable def bellBasis : OrthonormalBasis (Fin 4) ℂ (Qubit ⊗[ℂ] Qubit) :=
  OrthonormalBasis.mk bell_orthonormal_family (by rw [bell_orthonormal.2])

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
def bellRaw : Fin 4 → Fin 2 × Fin 2 → ℂ
  | 0, p => if p = (0, 0) then 1 else if p = (1, 1) then 1 else 0
  | 1, p => if p = (0, 0) then 1 else if p = (1, 1) then -1 else 0
  | 2, p => if p = (0, 1) then 1 else if p = (1, 0) then 1 else 0
  | 3, p => if p = (0, 1) then 1 else if p = (1, 0) then -1 else 0

/-- The four Bell states in coordinates, each normalised by `1/√2`. -/
noncomputable def bellVec (k : Fin 4) : TwoQubit :=
  WithLp.toLp 2 (fun p => (Real.sqrt 2 : ℂ)⁻¹ * bellRaw k p)

/-- The four Bell states form an orthonormal family of `EuclideanSpace ℂ (Fin 2 × Fin 2)`. -/
theorem bellVec_orthonormal_family : Orthonormal ℂ bellVec := by
  constructor
  · intro i
    rw [EuclideanSpace.norm_eq]
    fin_cases i <;>
      simp [bellVec, bellRaw, Fintype.sum_prod_type, Fin.sum_univ_succ, Complex.norm_real] <;>
      rw [show (2 : ℝ)⁻¹ + 2⁻¹ = 1 by norm_num]
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [bellVec, bellRaw, PiLp.inner_apply, Fintype.sum_prod_type, Fin.sum_univ_succ]

/-- The four Bell states form an orthonormal basis of `EuclideanSpace ℂ (Fin 2 × Fin 2)`. -/
theorem bellVec_orthonormal :
    Orthonormal ℂ bellVec ∧ Submodule.span ℂ (Set.range bellVec) = ⊤ := by
  refine ⟨bellVec_orthonormal_family, ?_⟩
  have hcard : Fintype.card (Fin 4) = Module.finrank ℂ TwoQubit := by
    simp [finrank_euclideanSpace]
  have := (basisOfOrthonormalOfCardEqFinrank bellVec_orthonormal_family hcard).span_eq
  rwa [coe_basisOfOrthonormalOfCardEqFinrank] at this

/-- The coordinate Bell states packaged as an `OrthonormalBasis`. -/
noncomputable def bellVecBasis : OrthonormalBasis (Fin 4) ℂ TwoQubit :=
  OrthonormalBasis.mk bellVec_orthonormal_family (by rw [bellVec_orthonormal.2])

@[simp] theorem bellVecBasis_apply (k : Fin 4) : bellVecBasis k = bellVec k := by
  simp [bellVecBasis]

end QC

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

