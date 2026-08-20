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
