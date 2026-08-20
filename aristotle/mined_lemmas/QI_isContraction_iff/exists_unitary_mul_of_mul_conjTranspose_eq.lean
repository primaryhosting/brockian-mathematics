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
# Uhlmann's theorem

For positive semidefinite matrices `ρ σ : Matrix n n ℂ` (in particular, for density matrices of
a finite dimensional quantum system) the *fidelity* is

`F(ρ, σ) = tr √(√ρ σ √ρ)`.

A vector of `ℂ^n ⊗ ℂ^m` is encoded here as a matrix `A : Matrix n m ℂ`; its reduced density
matrix on the first factor is `A * Aᴴ`, and the overlap of the vectors encoded by `A` and `B` is
`tr (Aᴴ * B)`.  Thus `A` is a *purification* of `ρ` exactly when `A * Aᴴ = ρ`.

**Uhlmann's theorem** (`QI.uhlmann_fidelity`) states that `F(ρ, σ)` is the maximum of
`‖tr (Aᴴ * B)‖` over all purifications `A` of `ρ` and `B` of `σ`.  The maximum is attained already
with a purifying system of the same dimension as the original one, and
`QI.overlap_le_fidelity` shows that no larger purifying system can do better.

The main ingredients proved along the way are a polar-type decomposition of matrices
(`QI.exists_unitary_mul_of_mul_conjTranspose_eq` and its rectangular contraction version), the
Hilbert–Schmidt Cauchy–Schwarz inequality (`QI.abs_trace_conjTranspose_mul_le`) and the bound
`‖tr (P * U)‖ ≤ tr P` for `P` positive semidefinite and `U` a contraction
(`QI.abs_trace_mul_contraction_le`).
-/

namespace QI

open Matrix
open scoped ComplexOrder MatrixOrder

/-! ### Norms of matrix-vector products -/


theorem exists_unitary_mul_of_mul_conjTranspose_eq {n : Type*} [Fintype n] [DecidableEq n]
    {A R : Matrix n n ℂ} (h : A * Aᴴ = R * Rᴴ) :
    ∃ W : Matrix n n ℂ, W ∈ unitary (Matrix n n ℂ) ∧ A = R * W := by
  classical
  obtain ⟨L, hL⟩ :=
    exists_isometryEquiv_comp (f := Matrix.toEuclideanLin Rᴴ) (g := Matrix.toEuclideanLin Aᴴ)
      (fun x => norm_conjTranspose_mulVec_eq A R h x)
  obtain ⟨V, hVmem, hVapp⟩ := exists_unitary_matrix_of_isometryEquiv L
  have hmul : V * Rᴴ = Aᴴ := by
    ext i j
    have hx := hL (WithLp.toLp 2 (Pi.single j (1 : ℂ)))
    have h1 : V *ᵥ (Rᴴ *ᵥ (Pi.single j (1 : ℂ))) = Aᴴ *ᵥ (Pi.single j (1 : ℂ)) := by
      have hfx : WithLp.ofLp (Matrix.toEuclideanLin Rᴴ (WithLp.toLp 2 (Pi.single j (1 : ℂ))))
          = Rᴴ *ᵥ Pi.single j (1 : ℂ) := by simp [toEuclideanLin_apply']
      have hgx : WithLp.ofLp (Matrix.toEuclideanLin Aᴴ (WithLp.toLp 2 (Pi.single j (1 : ℂ))))
          = Aᴴ *ᵥ Pi.single j (1 : ℂ) := by simp [toEuclideanLin_apply']
      have hcong := congrArg WithLp.ofLp hx
      rw [hgx] at hcong
      rw [← hcong, hVapp]
      congr 1
    rw [Matrix.mulVec_mulVec] at h1
    have := congrFun h1 i
    simpa [Matrix.mulVec_single] using this
  refine ⟨Vᴴ, Unitary.star_mem hVmem, ?_⟩
  have := congrArg Matrix.conjTranspose hmul
  simpa [Matrix.conjTranspose_mul] using this.symm

/-- **Rectangular polar-type decomposition.** If `A * Aᴴ = R * Rᴴ` with `A : Matrix n m ℂ` and
`R : Matrix n n ℂ`, then `A = R * W` for a matrix `W` such that both `W` and `Wᴴ` are
contractions. -/
