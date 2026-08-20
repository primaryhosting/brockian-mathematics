import Mathlib

/-!
# Uhlmann Fidelity
Category: Frontier Qi
Target: QI.uhlmann_fidelity
Statement: Fidelity equals the maximal overlap over purifications (Uhlmann's theorem).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

namespace QI

open Matrix
open scoped ComplexOrder MatrixOrder

/-! ### Isometries defined on the range of a linear map -/

section Isom

variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G]

/-- If `f` and `g` have the same norm pointwise, there is a linear isometry defined on the
range of `f` sending `f x` to `g x`. -/

theorem exists_factor [DecidableEq n] [DecidableEq k] {A : Matrix n m ℂ} {C : Matrix n k ℂ}
    (h : A * Aᴴ = C * Cᴴ) :
    ∃ V : Matrix k m ℂ, A = C * V ∧ IsContr Vᴴ := by
  have hCA : (Cᴴ)ᴴ * Cᴴ = (Aᴴ)ᴴ * Aᴴ := by
    simp only [Matrix.conjTranspose_conjTranspose]
    exact h.symm
  have hnorm : ∀ v : EuclideanSpace ℂ n,
      ‖(Matrix.toEuclideanLin Cᴴ) v‖ = ‖(Matrix.toEuclideanLin Aᴴ) v‖ :=
    fun v => norm_mulVec_congr hCA v.ofLp
  obtain ⟨T, hT, hTc⟩ :=
    exists_contraction_extension (Matrix.toEuclideanLin Cᴴ) (Matrix.toEuclideanLin Aᴴ) hnorm
  set W := Matrix.toEuclideanLin.symm T with hWdef
  have hlin : Matrix.toEuclideanLin W = T := by rw [hWdef, LinearEquiv.apply_symm_apply]
  have hWapply : ∀ z : k → ℂ, evec (W *ᵥ z) = T (evec z) := by
    intro z
    have : Matrix.toEuclideanLin W (evec z) = T (evec z) := by rw [hlin]
    exact this
  refine ⟨Wᴴ, ?_, ?_⟩
  · have hAW : Aᴴ = W * Cᴴ := by
      rw [Matrix.ext_iff_mulVec]
      intro x
      refine evec_injective ?_
      rw [← Matrix.mulVec_mulVec, hWapply]
      have h1 : evec (Cᴴ *ᵥ x) = Matrix.toEuclideanLin Cᴴ (evec x) := rfl
      rw [h1, hT (evec x)]
      rfl
    have := congrArg Matrix.conjTranspose hAW
    simpa using this
  · intro z
    rw [Matrix.conjTranspose_conjTranspose, hWapply z]
    exact hTc _

/-- Trace-norm duality bound: `|tr (Nᴴ W)| ≤ tr √(Nᴴ N)` for any contraction `W`. -/
