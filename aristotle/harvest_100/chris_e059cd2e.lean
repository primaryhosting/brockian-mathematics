import Mathlib

/-!
# No Cloning
Category: Quantum Computing
Target: QC.no_cloning
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


open scoped ComplexConjugate InnerProductSpace

namespace QC

/-- The state space of one qubit, `ℂ²` with the Euclidean (Hilbert) structure. -/
noncomputable abbrev Qubit := EuclideanSpace ℂ (Fin 2)

/-- The state space of two qubits, i.e. `Qubit ⊗ Qubit` realized concretely as
functions on `Fin 2 × Fin 2`. -/
noncomputable abbrev Qubit2 := EuclideanSpace ℂ (Fin 2 × Fin 2)

/-- The tensor product of two qubit states. -/
noncomputable def tens (a b : Qubit) : Qubit2 := WithLp.toLp 2 (fun p => a p.1 * b p.2)

/-- The inner product on the tensor product factorizes:
`⟪a ⊗ b, c ⊗ d⟫ = ⟪a, c⟫ * ⟪b, d⟫`. -/
lemma inner_tens (a b c d : Qubit) :
    ⟪tens a b, tens c d⟫_ℂ = ⟪a, c⟫_ℂ * ⟪b, d⟫_ℂ := by
  simp only [tens, PiLp.inner_apply, Fintype.sum_prod_type, RCLike.inner_apply,
    Finset.sum_mul_sum]
  simp [map_mul, mul_mul_mul_comm]

/-- The computational basis state `|0⟩`. -/
noncomputable def q0 : Qubit := !₂[1, 0]

/-- The state `|+⟩ = (|0⟩ + |1⟩)/√2`. -/
noncomputable def qplus : Qubit := !₂[(Real.sqrt 2)⁻¹, (Real.sqrt 2)⁻¹]

lemma norm_q0 : ‖q0‖ = 1 := by
  simp [q0, EuclideanSpace.norm_eq, Fin.sum_univ_two]

lemma norm_qplus : ‖qplus‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  simp [qplus, Fin.sum_univ_two, Complex.norm_real, abs_of_pos, Real.sq_sqrt]
  norm_num

lemma inner_q0_qplus : ⟪q0, qplus⟫_ℂ = ((Real.sqrt 2)⁻¹ : ℝ) := by
  simp [q0, qplus, PiLp.inner_apply, RCLike.inner_apply, Fin.sum_univ_two]

/-- **No-cloning, isometry version.** There is no linear isometry `U` of the two-qubit space
which maps `|ψ⟩ ⊗ |z⟩` to `|ψ⟩ ⊗ |ψ⟩` for every unit vector `|ψ⟩`, whatever the (unit) blank
state `|z⟩` is. -/
theorem no_cloning_isometry :
    ¬ ∃ (U : Qubit2 →ₗᵢ[ℂ] Qubit2) (z : Qubit), ‖z‖ = 1 ∧
      ∀ ψ : Qubit, ‖ψ‖ = 1 → U (tens ψ z) = tens ψ ψ := by
  rintro ⟨U, z, hz, hU⟩
  have hzz : ⟪z, z⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hz]; norm_num
  -- the cloner preserves inner products, forcing `c * c = c * 1` for `c = ⟪q0, qplus⟫`
  have key : ⟪q0, qplus⟫_ℂ * ⟪q0, qplus⟫_ℂ = ⟪q0, qplus⟫_ℂ * 1 := by
    have h := U.inner_map_map (tens q0 z) (tens qplus z)
    rw [hU q0 norm_q0, hU qplus norm_qplus, inner_tens, inner_tens, hzz] at h
    exact h
  have hcne : ⟪q0, qplus⟫_ℂ ≠ 0 := by
    rw [inner_q0_qplus]
    simp
  have hc1 : ((Real.sqrt 2)⁻¹ : ℝ) = (1 : ℂ) := by
    rw [← inner_q0_qplus]
    exact mul_left_cancel₀ hcne key
  have hr : ((Real.sqrt 2)⁻¹ : ℝ) = 1 := by exact_mod_cast hc1
  have h2 : Real.sqrt 2 = 1 := by
    rw [inv_eq_one] at hr
    exact hr
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  rw [h2] at hs
  norm_num at hs

/-- **No-cloning theorem.** There is no unitary `U` on the two-qubit space `ℂ² ⊗ ℂ²`
(a surjective linear isometry) such that `U (|ψ⟩ ⊗ |z⟩) = |ψ⟩ ⊗ |ψ⟩` for all unit vectors
`|ψ⟩`, for any fixed unit "blank" state `|z⟩`. -/
theorem no_cloning :
    ¬ ∃ (U : Qubit2 ≃ₗᵢ[ℂ] Qubit2) (z : Qubit), ‖z‖ = 1 ∧
      ∀ ψ : Qubit, ‖ψ‖ = 1 → U (tens ψ z) = tens ψ ψ := by
  rintro ⟨U, z, hz, hU⟩
  exact no_cloning_isometry ⟨U.toLinearIsometry, z, hz, hU⟩

end QC

#print axioms QC.no_cloning

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

