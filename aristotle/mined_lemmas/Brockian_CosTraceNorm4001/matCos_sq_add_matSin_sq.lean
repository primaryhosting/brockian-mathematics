import Mathlib

/-!
# A trace-norm bound for the matrix cosine

For a Hermitian complex matrix `A` we define the matrix cosine and sine by

  `cos A = (exp (I • A) + exp (-(I • A))) / 2`,  `sin A = (exp (I • A) - exp (-(I • A))) / (2 I)`,

and the trace norm (nuclear norm) of a matrix `M` as the sum of its singular values, i.e.
the sum of the square roots of the eigenvalues of `Mᴴ * M`.

The main result `Brockian.CosTraceNorm4001` states `‖cos A‖₁ ≤ card n`.
-/

namespace Brockian

open Matrix
open scoped ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The trace norm (nuclear norm) of a complex matrix: the sum of its singular values,
i.e. the sum of the square roots of the eigenvalues of `Mᴴ * M`. -/

lemma matCos_sq_add_matSin_sq (A : Matrix n n ℂ) :
    matCos A * matCos A + matSin A * matSin A = 1 := by
  set E := NormedSpace.exp (Complex.I • A)
  set F := NormedSpace.exp (-(Complex.I • A))
  have h1 : E * F = 1 := exp_mul_exp_neg A
  have h2 : F * E = 1 := exp_neg_mul_exp A
  have hplus : (E + F) * (E + F) = (E * E + F * F) + (E * F + F * E) := by noncomm_ring
  have hminus : (E - F) * (E - F) = (E * E + F * F) - (E * F + F * E) := by noncomm_ring
  have hexp : (E + F) * (E + F) = (E * E + F * F) + (2 : ℂ) • (1 : Matrix n n ℂ) := by
    rw [hplus, h1, h2]; module
  have hexm : (E - F) * (E - F) = (E * E + F * F) - (2 : ℂ) • (1 : Matrix n n ℂ) := by
    rw [hminus, h1, h2]; module
  have h4 : (2 * Complex.I) * (2 * Complex.I) = -4 := by
    linear_combination (4 : ℂ) * Complex.I_mul_I
  have hc : ((2 * Complex.I)⁻¹ * (2 * Complex.I)⁻¹ : ℂ) = -(4⁻¹ : ℂ) := by
    rw [← mul_inv, h4]; norm_num
  rw [matCos, matSin, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, hexp, hexm, hc]
  module

/-- The Hilbert–Schmidt bound: `tr ((cos A)ᴴ (cos A)) ≤ card n`. -/
