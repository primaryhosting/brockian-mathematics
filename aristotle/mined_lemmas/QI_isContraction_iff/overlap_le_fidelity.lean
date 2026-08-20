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


theorem overlap_le_fidelity {m : Type*} [Fintype m] [DecidableEq m] (hρ : ρ.PosSemidef)
    (hσ : σ.PosSemidef) {A B : Matrix n m ℂ} (hA : A * Aᴴ = ρ) (hB : B * Bᴴ = σ) :
    ‖(Aᴴ * B).trace‖ ≤ fidelity ρ σ := by
  classical
  set P : Matrix n n ℂ := CFC.sqrt ρ with hPdef
  set Q : Matrix n n ℂ := CFC.sqrt σ with hQdef
  have hP : P.PosSemidef := (CFC.sqrt_nonneg ρ).posSemidef
  have hQ : Q.PosSemidef := (CFC.sqrt_nonneg σ).posSemidef
  have hPP : P * P = ρ := CFC.sqrt_mul_sqrt_self ρ (by exact hρ.nonneg)
  have hQQ : Q * Q = σ := CFC.sqrt_mul_sqrt_self σ (by exact hσ.nonneg)
  have hPH : Pᴴ = P := hP.isHermitian
  have hQH : Qᴴ = Q := hQ.isHermitian
  have hNNH : (P * Q) * (P * Q)ᴴ = P * σ * P := by
    rw [Matrix.conjTranspose_mul, hPH, hQH, Matrix.mul_assoc, ← Matrix.mul_assoc Q Q P,
      hQQ, Matrix.mul_assoc]
  set R : Matrix n n ℂ := CFC.sqrt (P * σ * P) with hRdef
  have hNNHpsd : (P * σ * P).PosSemidef := by
    rw [← hNNH]
    exact Matrix.posSemidef_self_mul_conjTranspose _
  have hR : R.PosSemidef := (CFC.sqrt_nonneg _).posSemidef
  have hRR : R * R = P * σ * P := CFC.sqrt_mul_sqrt_self _ (by exact hNNHpsd.nonneg)
  have hRH : Rᴴ = R := hR.isHermitian
  obtain ⟨W, hWmem, hW⟩ :=
    exists_unitary_mul_of_mul_conjTranspose_eq (A := P * Q) (R := R) (by rw [hNNH, hRH, hRR])
  obtain ⟨W₁, hW₁, hW₁c, hW₁c'⟩ :=
    exists_contraction_mul_of_mul_conjTranspose_eq (A := A) (R := P) (by rw [hA, hPH, hPP])
  obtain ⟨W₂, hW₂, hW₂c, hW₂c'⟩ :=
    exists_contraction_mul_of_mul_conjTranspose_eq (A := B) (R := Q) (by rw [hB, hQH, hQQ])
  have hU : IsContraction (W * (W₂ * W₁ᴴ)) :=
    (isContraction_of_mem_unitary hWmem).mul (hW₂c.mul hW₁c')
  have hkey : (Aᴴ * B).trace = (R * (W * (W₂ * W₁ᴴ))).trace := by
    rw [hW₁, hW₂, Matrix.conjTranspose_mul, hPH]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc P Q W₂, hW]
    rw [Matrix.trace_mul_comm]
    simp [Matrix.mul_assoc]
  rw [hkey]
  exact abs_trace_mul_contraction_le hR hU

/-- **Uhlmann's theorem.**  The fidelity of two states `ρ, σ` of an `n`-dimensional system is the
maximum of the overlaps `|⟨ψ|φ⟩|` over all purifications `ψ` of `ρ` and `φ` of `σ` living in
`ℂ^n ⊗ ℂ^n`.  A vector of `ℂ^n ⊗ ℂ^n` is encoded as a matrix `A : Matrix n n ℂ`; then its
reduced density matrix on the first factor is `A * Aᴴ`, and the overlap of the vectors encoded by
`A` and `B` is `tr (Aᴴ * B)`. -/
