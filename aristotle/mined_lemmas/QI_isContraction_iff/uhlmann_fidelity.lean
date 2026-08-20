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


theorem uhlmann_fidelity (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) :
    IsGreatest {x : ℝ | ∃ A B : Matrix n n ℂ, A * Aᴴ = ρ ∧ B * Bᴴ = σ ∧ x = ‖(Aᴴ * B).trace‖}
      (fidelity ρ σ) := by
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
  have hfid : fidelity ρ σ = R.trace.re := rfl
  obtain ⟨W, hWmem, hW⟩ :=
    exists_unitary_mul_of_mul_conjTranspose_eq (A := P * Q) (R := R) (by rw [hNNH, hRH, hRR])
  obtain ⟨hW1, hW2⟩ := Unitary.mem_iff.mp hWmem
  have hWW : Wᴴ * W = 1 := by simpa using hW1
  have hWW' : W * Wᴴ = 1 := by simpa using hW2
  have htraceR : ‖R.trace‖ = R.trace.re := by
    have h0 : (0 : ℂ) ≤ R.trace := hR.trace_nonneg
    have him : R.trace.im = 0 := ((Complex.le_def.mp h0).2).symm
    rw [Complex.norm_def, Complex.normSq_apply, him]
    simpa using Real.sqrt_mul_self (trace_re_nonneg hR)
  constructor
  · -- the value is attained
    refine ⟨P, Q * Wᴴ, ?_, ?_, ?_⟩
    · rw [hPH, hPP]
    · rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc,
        ← Matrix.mul_assoc Wᴴ W Qᴴ, hWW, Matrix.one_mul, hQH, hQQ]
    · rw [hPH, ← Matrix.mul_assoc, hW, Matrix.mul_assoc, hWW', Matrix.mul_one, hfid, htraceR]
  · -- the value is an upper bound
    rintro x ⟨A, B, hA, hB, rfl⟩
    exact overlap_le_fidelity hρ hσ hA hB

end Uhlmann

end QI

