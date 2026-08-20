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

lemma trace_cos_sq_le {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    (Matrix.trace ((matCos A)ᴴ * matCos A)).re ≤ (Fintype.card n : ℝ) := by
  have hC : (matCos A)ᴴ = matCos A := (matCos_isHermitian hA).eq
  have hS : (matSin A)ᴴ = matSin A := (matSin_isHermitian hA).eq
  have hsplit : matCos A * matCos A = 1 - matSin A * matSin A := by
    have := matCos_sq_add_matSin_sq A
    linear_combination (norm := module) this
  have hpsd : (matSin A * matSin A).PosSemidef := by
    have := Matrix.posSemidef_conjTranspose_mul_self (matSin A)
    rwa [hS] at this
  have hnn : (0 : ℂ) ≤ Matrix.trace (matSin A * matSin A) := hpsd.trace_nonneg
  have hre : 0 ≤ (Matrix.trace (matSin A * matSin A)).re := (Complex.nonneg_iff.mp hnn).1
  rw [hC, hsplit, Matrix.trace_sub, Matrix.trace_one]
  simp only [Complex.sub_re, Complex.natCast_re]
  linarith

