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

/-- The state space of two qubits, `ℂ² ⊗ ℂ²`, modelled as the Hilbert space
`EuclideanSpace ℂ (Fin 2 × Fin 2)`: functions on pairs of bits with the standard
Hermitian inner product.  The basis vector indexed by `(a, b)` is the product state
`|a⟩ ⊗ |b⟩`. -/
abbrev TwoQubit := EuclideanSpace ℂ (Fin 2 × Fin 2)

/-- The product state `|a⟩ ⊗ |b⟩` of two qubit basis states. -/
noncomputable def ket (a b : Fin 2) : TwoQubit := EuclideanSpace.single (a, b) 1

/-- The coefficients of the four Bell states in the computational basis
`|00⟩, |01⟩, |10⟩, |11⟩`:

* `i = 0` : `Φ⁺ = (|00⟩ + |11⟩)/√2`
* `i = 1` : `Φ⁻ = (|00⟩ - |11⟩)/√2`
* `i = 2` : `Ψ⁺ = (|01⟩ + |10⟩)/√2`
* `i = 3` : `Ψ⁻ = (|01⟩ - |10⟩)/√2`
-/
noncomputable def bellCoeff (i : Fin 4) (p : Fin 2 × Fin 2) : ℂ :=
  (Real.sqrt 2 : ℂ)⁻¹ *
    match i, p.1, p.2 with
    | 0, 0, 0 => 1
    | 0, 1, 1 => 1
    | 1, 0, 0 => 1
    | 1, 1, 1 => -1
    | 2, 0, 1 => 1
    | 2, 1, 0 => 1
    | 3, 0, 1 => 1
    | 3, 1, 0 => -1
    | _, _, _ => 0

/-- The four Bell states, as vectors of the two-qubit space `ℂ² ⊗ ℂ²`. -/
noncomputable def bell (i : Fin 4) : TwoQubit := WithLp.toLp 2 (bellCoeff i)

/-- The Bell states, written as (normalized) superpositions of product states. -/
theorem bell_eq :
    bell 0 = (Real.sqrt 2 : ℂ)⁻¹ • (ket 0 0 + ket 1 1) ∧
    bell 1 = (Real.sqrt 2 : ℂ)⁻¹ • (ket 0 0 - ket 1 1) ∧
    bell 2 = (Real.sqrt 2 : ℂ)⁻¹ • (ket 0 1 + ket 1 0) ∧
    bell 3 = (Real.sqrt 2 : ℂ)⁻¹ • (ket 0 1 - ket 1 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · ext p
    obtain ⟨a, b⟩ := p
    fin_cases a <;> fin_cases b <;>
      simp [bell, bellCoeff, ket, EuclideanSpace.single_apply, Prod.ext_iff]

/-- The inner product on the two-qubit space, expanded over the computational basis. -/
theorem inner_eq (x y : TwoQubit) :
    inner ℂ x y = ∑ p : Fin 2 × Fin 2, conj (x.ofLp p) * y.ofLp p := by
  rw [PiLp.inner_apply]
  simp [RCLike.inner_apply, mul_comm]

private theorem inv_sqrt_two_sq : ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) = 1 / 2 := by
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  norm_num

/-- The four Bell states are orthonormal. -/
theorem bell_orthonormal_family : Orthonormal ℂ bell := by
  rw [orthonormal_iff_ite]
  intro i j
  rw [inner_eq]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, bell, bellCoeff, WithLp.ofLp_toLp]
  fin_cases i <;> fin_cases j <;>
    simp [map_mul, Complex.conj_ofReal, ← Complex.ofReal_inv, inv_sqrt_two_sq] <;>
    ring_nf <;>
    simp [inv_sqrt_two_sq] <;>
    ring_nf <;>
    rw [show ((Real.sqrt 2 : ℂ))⁻¹ ^ 2 = ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) by ring,
      inv_sqrt_two_sq] <;>
    ring

/-- **The four Bell states form an orthonormal basis of `ℂ² ⊗ ℂ²`.**
There is an orthonormal basis of the two-qubit space whose vectors are exactly the
four Bell states `Φ⁺, Φ⁻, Ψ⁺, Ψ⁻`. -/
theorem bell_orthonormal :
    Orthonormal ℂ bell ∧
      ∃ B : OrthonormalBasis (Fin 4) ℂ TwoQubit, ∀ i, B i = bell i := by
  refine ⟨bell_orthonormal_family, ?_⟩
  have hcard : Fintype.card (Fin 4) = Module.finrank ℂ TwoQubit := by simp
  have hspan : (⊤ : Submodule ℂ TwoQubit) ≤ Submodule.span ℂ (Set.range bell) := by
    have := (basisOfLinearIndependentOfCardEqFinrank
      bell_orthonormal_family.linearIndependent hcard).span_eq
    rw [coe_basisOfLinearIndependentOfCardEqFinrank] at this
    exact this.ge
  exact ⟨OrthonormalBasis.mk bell_orthonormal_family hspan, fun i => by
    simp [OrthonormalBasis.coe_mk]⟩

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

