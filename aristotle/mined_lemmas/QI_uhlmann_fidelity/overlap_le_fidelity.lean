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

lemma overlap_le_fidelity (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (A B : Matrix n n ℂ) (hA : A * Aᴴ = ρ) (hB : B * Bᴴ = σ) :
    ‖(Aᴴ * B).trace‖ ≤ fidelity ρ σ := by
  set sr := CFC.sqrt ρ with hsrdef
  set ss := CFC.sqrt σ with hssdef
  have hsrH : srᴴ = sr := (CFC.sqrt_nonneg ρ).posSemidef.isHermitian
  -- polar decompositions of the two purifications
  obtain ⟨U, hU, hAU⟩ := exists_unitary_polar A
  obtain ⟨V, hV, hBV⟩ := exists_unitary_polar B
  rw [hA] at hAU
  rw [hB] at hBV
  have hUU : Uᴴ * U = 1 := mul_eq_one_comm.1 hU
  -- polar decomposition of `√ρ √σ`
  obtain ⟨W, hW, hMW⟩ := exists_unitary_polar (sr * ss)
  rw [sqrt_mul_sqrt_mul_conjTranspose hσ] at hMW
  set Q := CFC.sqrt (sr * σ * sr) with hQdef
  have hQPSD : Q.PosSemidef := (CFC.sqrt_nonneg _).posSemidef
  set Y := W * V * Uᴴ with hYdef
  have hYH : Yᴴ = U * Vᴴ * Wᴴ := by
    rw [hYdef]
    simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have hYY : Y * Yᴴ = 1 := by
    rw [hYdef, hYH]
    calc W * V * Uᴴ * (U * Vᴴ * Wᴴ)
        = W * V * (Uᴴ * U) * Vᴴ * Wᴴ := by noncomm_ring
      _ = W * (V * Vᴴ) * Wᴴ := by rw [hUU]; noncomm_ring
      _ = 1 := by rw [hV, Matrix.mul_one, hW]
  have htrace : (Aᴴ * B).trace = (Q * Y).trace := by
    rw [hAU, hBV, Matrix.conjTranspose_mul, hsrH]
    calc (Uᴴ * sr * (ss * V)).trace = ((sr * ss) * V * Uᴴ).trace := by
          rw [show Uᴴ * sr * (ss * V) = Uᴴ * (sr * ss * V) by noncomm_ring,
            Matrix.trace_mul_comm]
          congr 1; noncomm_ring
      _ = (Q * Y).trace := by rw [hMW, hYdef]; congr 1; noncomm_ring
  rw [htrace]
  exact norm_trace_mul_unitary_le hQPSD hYY

/-- The fidelity is attained by a pair of purifications. -/
