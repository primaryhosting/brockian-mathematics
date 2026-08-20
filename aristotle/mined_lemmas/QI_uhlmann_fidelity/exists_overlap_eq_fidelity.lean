/-
# Uhlmann Fidelity
Category: Frontier Qi
Target: QI.uhlmann_fidelity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Uhlmann Fidelity
Category: Frontier Qi
Target: QI.uhlmann_fidelity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

This file proves **Uhlmann's theorem**: for positive semidefinite states `ρ`, `σ` on `ℂ^n`,
the fidelity `F(ρ, σ) = Tr √(√ρ σ √ρ)` is the *maximal* overlap `|⟪ψ, φ⟫|` taken over all
purifications `ψ` of `ρ` and `φ` of `σ` in `ℂ^n ⊗ ℂ^n`, where a purification of `ρ` is a
vector whose reduced density matrix (partial trace over the second factor) is `ρ`.

Neither quantum fidelity nor purifications (nor even the polar decomposition of a matrix)
are available in Mathlib, so everything is developed here from scratch:

* `QI.abs_trace_conjTranspose_mul_le`: Cauchy–Schwarz/AM–GM for the Hilbert–Schmidt
  inner product, `|Tr (Aᴴ B)| ≤ (‖A‖₂² + ‖B‖₂²) / 2`.
* `QI.exists_unitary_polar`: the polar decomposition `M = √(M Mᴴ) U` with `U` unitary,
  obtained by extending the isometry `√(M Mᴴ) x ↦ Mᴴ x` to a unitary of `ℂ^n`.
* `QI.norm_trace_mul_unitary_le`: `|Tr (Q Y)| ≤ Tr Q` for `Q ≥ 0` and `Y` unitary.
* `QI.uhlmann_fidelity_matrix` and `QI.uhlmann_fidelity`: Uhlmann's theorem, in matrix
  form and in terms of purifying vectors.
-/

open scoped MatrixOrder ComplexOrder BigOperators
open Matrix

namespace QI

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## The Hilbert–Schmidt (Frobenius) inner product -/

/-- The squared Frobenius (Hilbert–Schmidt) norm of a matrix. -/

lemma exists_overlap_eq_fidelity (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) :
    ∃ A B : Matrix n n ℂ, A * Aᴴ = ρ ∧ B * Bᴴ = σ ∧
      fidelity ρ σ = ‖(Aᴴ * B).trace‖ := by
  set sr := CFC.sqrt ρ with hsrdef
  set ss := CFC.sqrt σ with hssdef
  have hsrH : srᴴ = sr := (CFC.sqrt_nonneg ρ).posSemidef.isHermitian
  have hssH : ssᴴ = ss := (CFC.sqrt_nonneg σ).posSemidef.isHermitian
  have hsrsr : sr * sr = ρ := CFC.sqrt_mul_sqrt_self ρ hρ.nonneg
  have hssss : ss * ss = σ := CFC.sqrt_mul_sqrt_self σ hσ.nonneg
  obtain ⟨W, hW, hMW⟩ := exists_unitary_polar (sr * ss)
  rw [sqrt_mul_sqrt_mul_conjTranspose hσ] at hMW
  set Q := CFC.sqrt (sr * σ * sr) with hQdef
  have hQPSD : Q.PosSemidef := (CFC.sqrt_nonneg _).posSemidef
  have hWW : Wᴴ * W = 1 := mul_eq_one_comm.1 hW
  have hFre : ((fidelity ρ σ : ℝ) : ℂ) = Q.trace := by
    have h0 : 0 ≤ Q.trace := hQPSD.trace_nonneg
    rw [Complex.nonneg_iff] at h0
    have hf : fidelity ρ σ = Q.trace.re := rfl
    rw [hf, Complex.ext_iff]
    exact ⟨rfl, by simpa using h0.2⟩
  refine ⟨sr, ss * Wᴴ, by rw [hsrH, hsrsr], ?_, ?_⟩
  · rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hssH]
    calc ss * Wᴴ * (W * ss) = ss * (Wᴴ * W) * ss := by noncomm_ring
      _ = σ := by rw [hWW, Matrix.mul_one, hssss]
  · have h2 : (srᴴ * (ss * Wᴴ)).trace = Q.trace := by
      rw [hsrH]
      calc (sr * (ss * Wᴴ)).trace = (Q * W * Wᴴ).trace := by
            rw [show sr * (ss * Wᴴ) = (sr * ss) * Wᴴ by noncomm_ring, hMW]
        _ = (Q * (W * Wᴴ)).trace := by rw [Matrix.mul_assoc]
        _ = Q.trace := by rw [hW, Matrix.mul_one]
    rw [h2, ← hFre, Complex.norm_real, Real.norm_of_nonneg (fidelity_nonneg hσ)]

/-- **Uhlmann's theorem**, matrix form: the fidelity `Tr √(√ρ σ √ρ)` is the greatest
overlap `|Tr (Aᴴ B)|` over matrices `A`, `B` with `A Aᴴ = ρ` and `B Bᴴ = σ`. -/
