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

/-!
# The no-cloning theorem

We work with a single qubit space `QC.H := EuclideanSpace ℂ (Fin 2)` and model the
two-fold tensor product `H ⊗ H` concretely as `QC.HH := EuclideanSpace ℂ (Fin 2 × Fin 2)`,
with the elementary tensor `QC.tens a b` given by `(a ⊗ b) (i, j) = a i * b j`.
This satisfies the defining property of the tensor inner product,
`⟪a ⊗ b, c ⊗ d⟫ = ⟪a, c⟫ * ⟪b, d⟫` (see `QC.inner_tens`).

The main results state that there is no unitary `U` on `H ⊗ H` with
`U (ψ ⊗ |0⟩) = ψ ⊗ ψ` for every unit vector `ψ`, both for `U` a linear isometry
equivalence (`QC.no_cloning`) and for `U` a unitary element of the algebra of
continuous linear operators (`QC.no_cloning_unitary`).
-/

namespace QC

/-- The state space of one qubit. -/
abbrev H : Type := EuclideanSpace ℂ (Fin 2)

/-- The state space of two qubits, i.e. `H ⊗ H`. -/
abbrev HH : Type := EuclideanSpace ℂ (Fin 2 × Fin 2)

/-- The elementary tensor `a ⊗ b` of two qubit states. -/
noncomputable def tens (a b : H) : HH := WithLp.toLp 2 (fun p => a.ofLp p.1 * b.ofLp p.2)

/-- The inner product of elementary tensors factors. -/
lemma inner_tens (a b c d : H) :
    inner ℂ (tens a b) (tens c d) = inner ℂ a c * inner ℂ b d := by
  simp [tens, PiLp.inner_apply, Fintype.sum_prod_type]
  ring

/-- The computational basis state `|0⟩`. -/
noncomputable def q0 : H := EuclideanSpace.single 0 1

/-- The computational basis state `|1⟩`. -/
noncomputable def q1 : H := EuclideanSpace.single 1 1

/-- The state `|+⟩ = (|0⟩ + |1⟩)/√2`. -/
noncomputable def qp : H := (((Real.sqrt 2 : ℝ) : ℂ))⁻¹ • (q0 + q1)

lemma norm_q0 : ‖q0‖ = 1 := by simp [q0]

lemma norm_qp : ‖qp‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  simp [qp, q0, q1, EuclideanSpace.single_apply, Fin.sum_univ_two]
  norm_num

lemma inner_q0_q0 : inner ℂ q0 q0 = 1 := by simp [q0]

lemma inner_q0_qp : inner ℂ q0 qp = (((Real.sqrt 2 : ℝ) : ℂ))⁻¹ := by
  simp [q0, q1, qp, EuclideanSpace.inner_single_left, EuclideanSpace.single_apply]

/-- Key step: no inner-product-preserving map on `H ⊗ H` can clone all unit vectors. -/
theorem no_cloning_of_inner_preserving (U : HH → HH)
    (hU : ∀ x y : HH, inner ℂ (U x) (U y) = inner ℂ x y)
    (hclone : ∀ ψ : H, ‖ψ‖ = 1 → U (tens ψ q0) = tens ψ ψ) : False := by
  have h1 := hU (tens q0 q0) (tens qp q0)
  rw [hclone q0 norm_q0, hclone qp norm_qp, inner_tens, inner_tens, inner_q0_q0,
    inner_q0_qp] at h1
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  have hc : (((Real.sqrt 2 : ℝ) : ℂ))⁻¹ ≠ 0 := by
    simp [hs]
  have h2 : (((Real.sqrt 2 : ℝ) : ℂ))⁻¹ = 1 := by
    have := mul_left_cancel₀ hc (by simpa using h1.symm :
      (((Real.sqrt 2 : ℝ) : ℂ))⁻¹ * (((Real.sqrt 2 : ℝ) : ℂ))⁻¹
        = (((Real.sqrt 2 : ℝ) : ℂ))⁻¹ * 1)
    simp at this
  have h3 : Real.sqrt 2 = 1 := by
    have : ((Real.sqrt 2 : ℝ) : ℂ) = 1 := by
      field_simp at h2
      exact_mod_cast h2.symm
    exact_mod_cast this
  have h4 : (2 : ℝ) = 1 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), h3]
  norm_num at h4

/-- **No-cloning theorem** (unitary = linear isometry equivalence form):
there is no unitary `U` on `H ⊗ H` with `U (ψ ⊗ |0⟩) = ψ ⊗ ψ` for all unit vectors `ψ`. -/
theorem no_cloning :
    ¬ ∃ U : HH ≃ₗᵢ[ℂ] HH, ∀ ψ : H, ‖ψ‖ = 1 → U (tens ψ q0) = tens ψ ψ := by
  rintro ⟨U, hU⟩
  exact no_cloning_of_inner_preserving U (fun x y => U.inner_map_map x y) hU

/-- **No-cloning theorem** (unitary element of the operator algebra form). -/
theorem no_cloning_unitary :
    ¬ ∃ U : HH →L[ℂ] HH, U ∈ unitary (HH →L[ℂ] HH) ∧
      ∀ ψ : H, ‖ψ‖ = 1 → U (tens ψ q0) = tens ψ ψ := by
  rintro ⟨U, hUu, hU⟩
  refine no_cloning_of_inner_preserving U (fun x y => ?_) hU
  have h : star U * U = 1 := hUu.1
  calc inner ℂ (U x) (U y) = inner ℂ ((ContinuousLinearMap.adjoint U) (U x)) y := by
        rw [ContinuousLinearMap.adjoint_inner_left]
    _ = inner ℂ x y := by
        rw [← ContinuousLinearMap.star_eq_adjoint,
          show (star U) (U x) = ((star U) * U) x from rfl, h]
        rfl

end QC

