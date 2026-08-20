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


theorem abs_trace_mul_contraction_le {n : Type*} [Fintype n] [DecidableEq n] {P U : Matrix n n ℂ}
    (hP : P.PosSemidef) (hU : IsContraction U) : ‖(P * U).trace‖ ≤ P.trace.re := by
  set S : Matrix n n ℂ := CFC.sqrt P with hSdef
  have hS : S.PosSemidef := (CFC.sqrt_nonneg P).posSemidef
  have hSS : S * S = P := CFC.sqrt_mul_sqrt_self P (by exact hP.nonneg)
  have hSH : Sᴴ = S := hS.isHermitian
  have htr : (P * U).trace = (Sᴴ * (U * S)).trace := by
    rw [hSH, ← hSS, Matrix.mul_assoc, Matrix.trace_mul_comm S (S * U), Matrix.mul_assoc]
  have h1 : (Sᴴ * S).trace = P.trace := by rw [hSH, hSS]
  have hD : (Sᴴ * (1 - Uᴴ * U) * S).PosSemidef := hU.conjTranspose_mul_mul_same S
  have hDexp : Sᴴ * (1 - Uᴴ * U) * S = Sᴴ * S - (U * S)ᴴ * (U * S) := by
    rw [Matrix.conjTranspose_mul]
    noncomm_ring
  have h2 : ((U * S)ᴴ * (U * S)).trace.re ≤ P.trace.re := by
    have h3 := trace_re_nonneg hD
    rw [hDexp, Matrix.trace_sub, Complex.sub_re, h1] at h3
    linarith
  have hcs := abs_trace_conjTranspose_mul_le S (U * S)
  rw [h1] at hcs
  rw [htr]
  refine hcs.trans ?_
  calc Real.sqrt P.trace.re * Real.sqrt (((U * S)ᴴ * (U * S)).trace.re)
      ≤ Real.sqrt P.trace.re * Real.sqrt P.trace.re :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h2) (Real.sqrt_nonneg _)
    _ = P.trace.re := Real.mul_self_sqrt (trace_re_nonneg hP)

/-- For `P` positive semidefinite and `U` unitary, `|tr (P U)| ≤ tr P`. -/
