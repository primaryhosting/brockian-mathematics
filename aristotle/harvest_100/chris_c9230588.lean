/-!
# Bell Orthonormal
Category: Quantum Computing
Target: QC.bell_orthonormal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped ComplexConjugate

namespace QC

/-- The state space of two qubits, `ℂ² ⊗ ℂ²`, realized concretely as the
finite-dimensional Hilbert space `EuclideanSpace ℂ (Fin 2 × Fin 2)`, whose standard basis
is the computational basis `|00⟩, |01⟩, |10⟩, |11⟩`. -/
abbrev TwoQubit := EuclideanSpace ℂ (Fin 2 × Fin 2)

/-- The normalization constant `1/√2`. -/
noncomputable def invSqrt2 : ℂ := (Real.sqrt 2 : ℝ)⁻¹

lemma conj_invSqrt2 : conj invSqrt2 = invSqrt2 := by
  simp [invSqrt2, ← Complex.ofReal_inv]

lemma invSqrt2_mul_self : invSqrt2 * invSqrt2 = 1 / 2 := by
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    norm_cast
    rw [Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  have hne : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    simp [Real.sqrt_eq_zero']
  field_simp [invSqrt2]
  linear_combination -h2

/-- Coordinates of the four Bell states in the computational basis.

* `bellCoord 0` is `Φ⁺ = (|00⟩ + |11⟩)/√2`
* `bellCoord 1` is `Φ⁻ = (|00⟩ - |11⟩)/√2`
* `bellCoord 2` is `Ψ⁺ = (|01⟩ + |10⟩)/√2`
* `bellCoord 3` is `Ψ⁻ = (|01⟩ - |10⟩)/√2`
-/
noncomputable def bellCoord : Fin 4 → (Fin 2 × Fin 2) → ℂ := fun i p =>
  match i, p with
  | 0, (0, 0) => invSqrt2
  | 0, (1, 1) => invSqrt2
  | 1, (0, 0) => invSqrt2
  | 1, (1, 1) => -invSqrt2
  | 2, (0, 1) => invSqrt2
  | 2, (1, 0) => invSqrt2
  | 3, (0, 1) => invSqrt2
  | 3, (1, 0) => -invSqrt2
  | _, _ => 0

/-- The four Bell states, as vectors of the two-qubit space. -/
noncomputable def bell (i : Fin 4) : TwoQubit := WithLp.toLp 2 (bellCoord i)

lemma inner_bell (i j : Fin 4) :
    inner ℂ (bell i) (bell j) = ∑ p : Fin 2 × Fin 2, conj (bellCoord i p) * bellCoord j p := by
  simp [bell, PiLp.inner_apply, RCLike.inner_apply, mul_comm]

lemma inner_bell_eq_ite (i j : Fin 4) :
    inner ℂ (bell i) (bell j) = if i = j then 1 else 0 := by
  rw [inner_bell]
  fin_cases i <;> fin_cases j <;>
    simp [bellCoord, Fintype.sum_prod_type, Fin.sum_univ_succ, conj_invSqrt2,
      invSqrt2_mul_self] <;>
    ring

/-- The four Bell states are orthonormal. -/
theorem bell_orthonormal_family : Orthonormal ℂ bell :=
  orthonormal_iff_ite.2 inner_bell_eq_ite

/-- The four Bell states span the two-qubit space, hence form a (linear) basis. -/
noncomputable def bellLinearBasis : Module.Basis (Fin 4) ℂ TwoQubit :=
  basisOfLinearIndependentOfCardEqFinrank bell_orthonormal_family.linearIndependent
    (by simp)

lemma coe_bellLinearBasis : ⇑bellLinearBasis = bell :=
  coe_basisOfLinearIndependentOfCardEqFinrank _ _

/-- The four Bell states, packaged as an orthonormal basis of the two-qubit space
`ℂ² ⊗ ℂ² ≅ EuclideanSpace ℂ (Fin 2 × Fin 2)`. -/
noncomputable def bellBasis : OrthonormalBasis (Fin 4) ℂ TwoQubit :=
  bellLinearBasis.toOrthonormalBasis (by rw [coe_bellLinearBasis]; exact bell_orthonormal_family)

@[simp] lemma coe_bellBasis : ⇑bellBasis = bell := by
  rw [bellBasis, Module.Basis.coe_toOrthonormalBasis, coe_bellLinearBasis]

/-- **The four Bell states form an orthonormal basis of `ℂ² ⊗ ℂ²`.**
They are pairwise orthogonal unit vectors and they span the whole two-qubit state space. -/
theorem bell_orthonormal :
    Orthonormal ℂ bell ∧ Submodule.span ℂ (Set.range bell) = ⊤ :=
  ⟨bell_orthonormal_family, by
    rw [← coe_bellLinearBasis]; exact bellLinearBasis.span_eq⟩

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

