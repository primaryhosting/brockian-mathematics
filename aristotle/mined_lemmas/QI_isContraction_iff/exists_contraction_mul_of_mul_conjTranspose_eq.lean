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


theorem exists_contraction_mul_of_mul_conjTranspose_eq {n m : Type*} [Fintype n] [Fintype m]
    [DecidableEq n] [DecidableEq m] {A : Matrix n m ℂ} {R : Matrix n n ℂ} (h : A * Aᴴ = R * Rᴴ) :
    ∃ W : Matrix n m ℂ, A = R * W ∧ IsContraction W ∧ IsContraction Wᴴ := by
  classical
  obtain ⟨L, hLcomp, hLcontr⟩ :=
    exists_contraction_comp (f := Matrix.toEuclideanLin Rᴴ) (g := Matrix.toEuclideanLin Aᴴ)
      (fun x => norm_conjTranspose_mulVec_eq A R h x)
  set V : Matrix m n ℂ := Matrix.toEuclideanLin.symm L with hVdef
  have hVcontr : IsContraction V := isContraction_toEuclideanLin_symm L hLcontr
  have hVapp : ∀ x : EuclideanSpace ℂ n, Matrix.toEuclideanLin V x = L x := by
    intro x; rw [hVdef, Matrix.toEuclideanLin.apply_symm_apply]
  have hmul : V * Rᴴ = Aᴴ := by
    ext i j
    have hx := hLcomp (WithLp.toLp 2 (Pi.single j (1 : ℂ)))
    have h1 : V *ᵥ (Rᴴ *ᵥ (Pi.single j (1 : ℂ))) = Aᴴ *ᵥ (Pi.single j (1 : ℂ)) := by
      have hfx : Matrix.toEuclideanLin V (Matrix.toEuclideanLin Rᴴ
            (WithLp.toLp 2 (Pi.single j (1 : ℂ))))
          = Matrix.toEuclideanLin Aᴴ (WithLp.toLp 2 (Pi.single j (1 : ℂ))) := by
        rw [hVapp, hx]
      have := congrArg WithLp.ofLp hfx
      simpa [toEuclideanLin_apply'] using this
    rw [Matrix.mulVec_mulVec] at h1
    have := congrFun h1 i
    simpa [Matrix.mulVec_single] using this
  refine ⟨Vᴴ, ?_, hVcontr.conjTranspose, ?_⟩
  · have := congrArg Matrix.conjTranspose hmul
    simpa [Matrix.conjTranspose_mul] using this.symm
  · simpa using hVcontr

/-! ### The Hilbert–Schmidt Cauchy–Schwarz inequality -/

/-- A matrix, viewed as a vector in the Hilbert space `EuclideanSpace ℂ (n × n)`. -/
private noncomputable def hsVec {n : Type*} [Fintype n] (M : Matrix n n ℂ) :
    EuclideanSpace ℂ (n × n) :=
  WithLp.toLp 2 (fun p : n × n => M p.1 p.2)

