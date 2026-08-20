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

lemma sqrt_mul_sqrt_mul_conjTranspose (hσ : σ.PosSemidef) :
    (CFC.sqrt ρ * CFC.sqrt σ) * (CFC.sqrt ρ * CFC.sqrt σ)ᴴ = CFC.sqrt ρ * σ * CFC.sqrt ρ := by
  have hsrH : (CFC.sqrt ρ)ᴴ = CFC.sqrt ρ := (CFC.sqrt_nonneg ρ).posSemidef.isHermitian
  have hssH : (CFC.sqrt σ)ᴴ = CFC.sqrt σ := (CFC.sqrt_nonneg σ).posSemidef.isHermitian
  have hssss : CFC.sqrt σ * CFC.sqrt σ = σ := CFC.sqrt_mul_sqrt_self σ hσ.nonneg
  rw [Matrix.conjTranspose_mul, hsrH, hssH]
  calc CFC.sqrt ρ * CFC.sqrt σ * (CFC.sqrt σ * CFC.sqrt ρ)
      = CFC.sqrt ρ * (CFC.sqrt σ * CFC.sqrt σ) * CFC.sqrt ρ := by noncomm_ring
    _ = CFC.sqrt ρ * σ * CFC.sqrt ρ := by rw [hssss]

