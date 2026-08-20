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
# The Robertson uncertainty relation

For two observables (bounded self-adjoint operators) `A`, `B` on a complex Hilbert space `H`
and a state `ψ`, the standard deviations satisfy

  `ΔA · ΔB ≥ ½ |⟨[A, B]⟩|`.

Here `⟨X⟩ = ⟪ψ, X ψ⟫` is the expectation value, `ΔA = ‖(A - ⟨A⟩) ψ‖`, and `[A, B] = AB - BA`.
The theorem `QC.stdDev_sq` confirms that for a unit vector `ψ` and a self-adjoint `A`,
`(ΔA)² = ⟨A²⟩ - ⟨A⟩²`, so `stdDev` is indeed the usual standard deviation.
-/

namespace QC

open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The expectation value `⟨A⟩ = ⟪ψ, A ψ⟫` of an operator `A` in the state `ψ`. -/

lemma inner_selfAdjoint_move {A : H →L[ℂ] H} (hA : IsSelfAdjoint A) (x y : H) :
    ⟪A x, y⟫_ℂ = ⟪x, A y⟫_ℂ := by
  conv_lhs => rw [← hA.star_eq]
  simp [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]

/-- The expectation value of a self-adjoint operator is real. -/
