/-
# Bell Orthonormal
Category: Quantum Computing
Target: QC.bell_orthonormal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QC

open scoped ComplexConjugate

/-- The two–qubit state space `ℂ² ⊗ ℂ²`, modelled as the Hilbert space of functions
`Fin 2 × Fin 2 → ℂ` (the computational basis `|ij⟩` is indexed by pairs `(i, j)`). -/
abbrev Qubit2 := EuclideanSpace ℂ (Fin 2 × Fin 2)

/-- The normalisation constant `1/√2`. -/
noncomputable def invSqrt2 : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)⁻¹

lemma invSqrt2_conj : conj invSqrt2 = invSqrt2 := by
  simp [invSqrt2, ← Complex.ofReal_inv, Complex.conj_ofReal]

lemma invSqrt2_mul_self : invSqrt2 * invSqrt2 = 1 / 2 := by
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  rw [invSqrt2, ← mul_inv, h2]
  norm_num

/-- The (unnormalised) coefficients of the four Bell states in the computational basis. -/
def bellCoeff (k : Fin 4) (p : Fin 2 × Fin 2) : ℂ :=
  match k, p.1, p.2 with
  | 0, 0, 0 => 1
  | 0, 1, 1 => 1
  | 1, 0, 0 => 1
  | 1, 1, 1 => -1
  | 2, 0, 1 => 1
  | 2, 1, 0 => 1
  | 3, 0, 1 => 1
  | 3, 1, 0 => -1
  | _, _, _ => 0

/-- The four Bell states
`Φ⁺ = (|00⟩+|11⟩)/√2`, `Φ⁻ = (|00⟩-|11⟩)/√2`,
`Ψ⁺ = (|01⟩+|10⟩)/√2`, `Ψ⁻ = (|01⟩-|10⟩)/√2`. -/
noncomputable def bell (k : Fin 4) : Qubit2 :=
  WithLp.toLp 2 (fun p => invSqrt2 * bellCoeff k p)

lemma inner_bell (j k : Fin 4) :
    (inner ℂ (bell j) (bell k) : ℂ) =
      ∑ p : Fin 2 × Fin 2, conj (invSqrt2 * bellCoeff j p) * (invSqrt2 * bellCoeff k p) := by
  simp [bell, PiLp.inner_apply, RCLike.inner_apply, mul_comm]

/-- The Bell states are orthonormal. -/
theorem bell_orthonormal_family : Orthonormal ℂ bell := by
  rw [orthonormal_iff_ite]
  intro j k
  rw [inner_bell, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, map_mul, invSqrt2_conj]
  fin_cases j <;> fin_cases k <;>
    simp [bellCoeff, invSqrt2_mul_self] <;> ring

lemma card_eq_finrank : Fintype.card (Fin 4) = Module.finrank ℂ Qubit2 := by
  simp

/-- The Bell states span the whole two–qubit space. -/
theorem bell_span : Submodule.span ℂ (Set.range bell) = ⊤ := by
  rw [← coe_basisOfOrthonormalOfCardEqFinrank bell_orthonormal_family card_eq_finrank]
  exact Module.Basis.span_eq _

/-- **The four Bell states form an orthonormal basis of `ℂ² ⊗ ℂ²`**: they are pairwise
orthogonal unit vectors and they span the whole space. -/
theorem bell_orthonormal :
    Orthonormal ℂ bell ∧ Submodule.span ℂ (Set.range bell) = ⊤ :=
  ⟨bell_orthonormal_family, bell_span⟩

/-- The Bell basis, packaged as an orthonormal basis of the two–qubit space. -/
noncomputable def bellBasis : OrthonormalBasis (Fin 4) ℂ Qubit2 :=
  (basisOfOrthonormalOfCardEqFinrank bell_orthonormal_family card_eq_finrank).toOrthonormalBasis
    (by rw [coe_basisOfOrthonormalOfCardEqFinrank]; exact bell_orthonormal_family)

@[simp] lemma bellBasis_apply (k : Fin 4) : bellBasis k = bell k := by
  rw [bellBasis, Module.Basis.coe_toOrthonormalBasis,
    coe_basisOfOrthonormalOfCardEqFinrank]

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

