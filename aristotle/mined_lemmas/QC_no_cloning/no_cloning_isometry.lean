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
