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

lemma norm_trace_mul_unitary_le {Q Y : Matrix n n ℂ} (hQ : Q.PosSemidef) (hY : Y * Yᴴ = 1) :
    ‖(Q * Y).trace‖ ≤ Q.trace.re := by
  set R := CFC.sqrt Q with hRdef
  have hRPSD : R.PosSemidef := (CFC.sqrt_nonneg Q).posSemidef
  have hRH : Rᴴ = R := hRPSD.isHermitian
  have hRR : R * R = Q := CFC.sqrt_mul_sqrt_self Q hQ.nonneg
  have htr : ((Q.trace.re : ℝ) : ℂ) = Q.trace := by
    have h0 : 0 ≤ Q.trace := hQ.trace_nonneg
    rw [Complex.nonneg_iff] at h0
    rw [Complex.ext_iff]
    exact ⟨rfl, by simpa using h0.2⟩
  have hfR : frobSq R = Q.trace.re := by
    have h1 : ((frobSq R : ℝ) : ℂ) = ((Q.trace.re : ℝ) : ℂ) := by
      rw [← trace_conjTranspose_mul_self, hRH, hRR, htr]
    exact_mod_cast h1
  have hfRY : frobSq (R * Y) = Q.trace.re := by
    have h1 : ((frobSq (R * Y) : ℝ) : ℂ) = ((Q.trace.re : ℝ) : ℂ) := by
      rw [← trace_conjTranspose_mul_self, Matrix.conjTranspose_mul, hRH, htr]
      calc (Yᴴ * R * (R * Y)).trace = (Yᴴ * (R * R) * Y).trace := by
            rw [show Yᴴ * R * (R * Y) = Yᴴ * (R * R) * Y by noncomm_ring]
        _ = (Q * (Y * Yᴴ)).trace := by
            rw [hRR, show Yᴴ * Q * Y = Yᴴ * (Q * Y) by noncomm_ring, Matrix.trace_mul_comm]
            congr 1; noncomm_ring
        _ = Q.trace := by rw [hY, Matrix.mul_one]
    exact_mod_cast h1
  have hbound := abs_trace_conjTranspose_mul_le R (R * Y)
  rw [hRH, ← Matrix.mul_assoc, hRR, hfR, hfRY] at hbound
  linarith

/-! ## Fidelity and purifications -/

/-- The (Uhlmann) fidelity of two states `ρ`, `σ`, i.e. `Tr √(√ρ σ √ρ)`. -/
