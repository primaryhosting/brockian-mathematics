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

lemma abs_trace_conjTranspose_mul_le (A B : Matrix n n ℂ) :
    ‖(Aᴴ * B).trace‖ ≤ (frobSq A + frobSq B) / 2 := by
  have h : (Aᴴ * B).trace = ∑ i, ∑ j, star (A j i) * B j i := by
    simp [Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [h]
  calc ‖∑ i, ∑ j, star (A j i) * B j i‖ ≤ ∑ i, ∑ j, ‖A j i‖ * ‖B j i‖ := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => by simp)
    _ ≤ ∑ i, ∑ j, (‖A j i‖ ^ 2 + ‖B j i‖ ^ 2) / 2 := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        nlinarith [sq_nonneg (‖A j i‖ - ‖B j i‖)]
    _ = (frobSq A + frobSq B) / 2 := by
        rw [frobSq, frobSq, Finset.sum_comm (f := fun i j => ‖A i j‖ ^ 2),
          Finset.sum_comm (f := fun i j => ‖B i j‖ ^ 2)]
        simp only [add_div, Finset.sum_add_distrib, Finset.sum_div]

/-! ## Polar decomposition -/

/-- **Polar decomposition** of a square complex matrix: `M = √(M Mᴴ) U` for some unitary `U`.

The unitary is produced by extending the isometry `√(M Mᴴ) x ↦ Mᴴ x`, defined on the range
of `√(M Mᴴ)`, to a linear isometry of the whole space. -/
