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

theorem exists_polar [DecidableEq n] (M : Matrix n n ℂ) :
    ∃ U : Matrix n n ℂ, Uᴴ * U = 1 ∧ M = U * CFC.sqrt (Mᴴ * M) := by
  set P := CFC.sqrt (Mᴴ * M) with hPdef
  have h0 : (0 : Matrix n n ℂ) ≤ Mᴴ * M := (posSemidef_conjTranspose_mul_self M).nonneg
  have hPherm : Pᴴ = P := ((CFC.sqrt_nonneg (Mᴴ * M)).posSemidef).isHermitian
  have hPP : Mᴴ * M = Pᴴ * P := by rw [hPherm, hPdef, CFC.sqrt_mul_sqrt_self (Mᴴ * M)]
  have hnorm : ∀ v : EuclideanSpace ℂ n,
      ‖(Matrix.toEuclideanLin P) v‖ = ‖(Matrix.toEuclideanLin M) v‖ :=
    fun v => (norm_mulVec_congr hPP v.ofLp).symm
  obtain ⟨U₀, hU₀⟩ :=
    exists_isometry_extension (Matrix.toEuclideanLin P) (Matrix.toEuclideanLin M) hnorm
  set U := Matrix.toEuclideanLin.symm U₀.toLinearMap with hUdef
  have hlin : Matrix.toEuclideanLin U = U₀.toLinearMap := by
    rw [hUdef, LinearEquiv.apply_symm_apply]
  have hUapply : ∀ x : n → ℂ, evec (U *ᵥ x) = U₀ (evec x) := by
    intro x
    have : Matrix.toEuclideanLin U (evec x) = U₀.toLinearMap (evec x) := by rw [hlin]
    exact this
  refine ⟨U, ?_, ?_⟩
  · refine isUnitary_of_inner fun x y => ?_
    rw [← inner_evec, hUapply, hUapply, U₀.inner_map_map, inner_evec]
  · rw [Matrix.ext_iff_mulVec]
    intro y
    refine evec_injective ?_
    rw [← Matrix.mulVec_mulVec, hUapply]
    have h1 : evec (P *ᵥ y) = Matrix.toEuclideanLin P (evec y) := rfl
    rw [h1, hU₀ (evec y)]
    rfl

/-- If `A Aᴴ = C Cᴴ` then `A = C V` for some `V` with `Vᴴ` a contraction. -/
